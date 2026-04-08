import streamlit as st
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import hashlib
import random
import json
import os
from datetime import datetime

# ── Page config ────────────────────────────────────────────────────────────────
st.set_page_config(
    page_title="ECC – Eliptik Eğri Kriptografisi",
    page_icon="🔐",
    layout="wide",
)

# ── Shared ECC implementation ──────────────────────────────────────────────────

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx     = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy     = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


class SECP256K1:
    p, a, b, n, G = P_SECP, 0, 7, N_SECP, (Gx, Gy)

    @staticmethod
    def mod_inv(n, mod=P_SECP):
        return pow(n % mod, mod - 2, mod)

    @classmethod
    def add(cls, P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2:
            if y1 != y2 or y1 == 0: return None
            return cls.double(P)
        lam = (y2 - y1) * cls.mod_inv(x2 - x1) % cls.p
        x3 = (lam * lam - x1 - x2) % cls.p
        y3 = (lam * (x1 - x3) - y1) % cls.p
        return (x3, y3)

    @classmethod
    def double(cls, P):
        if P is None: return None
        x1, y1 = P
        if y1 == 0: return None
        lam = (3 * x1 * x1 + cls.a) * cls.mod_inv(2 * y1) % cls.p
        x3 = (lam * lam - 2 * x1) % cls.p
        y3 = (lam * (x1 - x3) - y1) % cls.p
        return (x3, y3)

    @classmethod
    def scalar_mult(cls, k, P):
        k %= cls.n
        result, addend = None, P
        while k:
            if k & 1: result = cls.add(result, addend)
            addend = cls.double(addend)
            k >>= 1
        return result


class EllipticCurveReal:
    def __init__(self, a, b):
        self.a, self.b = a, b

    def add(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if abs(x1 - x2) < 1e-12 and abs(y1 + y2) < 1e-12: return None
        if abs(x1 - x2) < 1e-12 and abs(y1 - y2) < 1e-12: return self.double(P)
        lam = (y2 - y1) / (x2 - x1)
        x3 = lam ** 2 - x1 - x2
        y3 = lam * (x1 - x3) - y1
        return (x3, y3)

    def double(self, P):
        if P is None: return None
        x1, y1 = P
        if abs(y1) < 1e-12: return None
        lam = (3 * x1 ** 2 + self.a) / (2 * y1)
        x3 = lam ** 2 - 2 * x1
        y3 = lam * (x1 - x3) - y1
        return (x3, y3)


class EllipticCurveFinite:
    def __init__(self, a, b, p):
        self.a, self.b, self.p = a, b, p

    def mod_inv(self, n):
        return pow(n % self.p, self.p - 2, self.p)

    def add(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2:
            if y1 != y2 or y1 == 0: return None
            return self.double(P)
        lam = (y2 - y1) * self.mod_inv(x2 - x1) % self.p
        x3 = (lam * lam - x1 - x2) % self.p
        y3 = (lam * (x1 - x3) - y1) % self.p
        return (x3, y3)

    def double(self, P):
        if P is None: return None
        x1, y1 = P
        if y1 == 0: return None
        lam = (3 * x1 * x1 + self.a) * self.mod_inv(2 * y1) % self.p
        x3 = (lam * lam - 2 * x1) % self.p
        y3 = (lam * (x1 - x3) - y1) % self.p
        return (x3, y3)

    def get_all_points(self):
        pts = []
        for x in range(self.p):
            rhs = (x * x * x + self.a * x + self.b) % self.p
            for y in range(self.p):
                if y * y % self.p == rhs:
                    pts.append((x, y))
        return pts


def generate_keypair():
    d = random.randint(1, SECP256K1.n - 1)
    Q = SECP256K1.scalar_mult(d, SECP256K1.G)
    return d, Q


def hash_message(msg: bytes) -> int:
    return int.from_bytes(hashlib.sha256(msg).digest(), "big") 


def ecdsa_sign(msg: bytes, priv: int):
    e, n = hash_message(msg), SECP256K1.n
    r = s = 0
    while r == 0 or s == 0:
        k = random.randint(1, n - 1)
        R = SECP256K1.scalar_mult(k, SECP256K1.G)
        r = R[0] % n
        if r == 0: continue
        s = pow(k, n - 2, n) * (e + r * priv) % n
    return (r, s)


def ecdsa_verify(msg: bytes, sig, pub) -> bool:
    r, s = sig
    n = SECP256K1.n
    if not (1 <= r < n and 1 <= s < n): return False
    e = hash_message(msg)
    w  = pow(s, n - 2, n)
    u1, u2 = e * w % n, r * w % n
    pt = SECP256K1.add(
        SECP256K1.scalar_mult(u1, SECP256K1.G),
        SECP256K1.scalar_mult(u2, pub),
    )
    return pt is not None and pt[0] % n == r


def xor_encrypt(data: bytes, key: int) -> bytes:
    kb = key.to_bytes(32, "big")
    return bytes(b ^ kb[i % 32] for i, b in enumerate(data))


# ── Helpers ────────────────────────────────────────────────────────────────────

_CHAT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "chat_state.json")

def _chat_load():
    if os.path.exists(_CHAT_FILE):
        try:
            with open(_CHAT_FILE, "r") as f:
                return json.load(f)
        except Exception:
            pass
    return {"alice": None, "bob": None, "attacker": None, "messages": []}

def _chat_save(state):
    with open(_CHAT_FILE, "w") as f:
        json.dump(state, f)

def _pub_to_dict(Q):
    return {"x": hex(Q[0]), "y": hex(Q[1])}

def _dict_to_pub(d):
    return (int(d["x"], 16), int(d["y"], 16))


def draw_real_curve(ax, a, b, xlim=(-3, 4), ylim=(-6, 6)):
    x = np.linspace(xlim[0], xlim[1], 2000)
    y_sq = x ** 3 + a * x + b
    m = y_sq >= 0
    ax.plot(x[m],  np.sqrt(y_sq[m]),  "steelblue", lw=2)
    ax.plot(x[m], -np.sqrt(y_sq[m]),  "steelblue", lw=2)
    ax.axhline(0, color="gray", lw=0.7, ls="--")
    ax.axvline(0, color="gray", lw=0.7, ls="--")
    ax.set_xlim(*xlim); ax.set_ylim(*ylim)
    ax.grid(True, alpha=0.3)


# ── Sidebar navigation ─────────────────────────────────────────────────────────

PAGES = [
    "🏠 Giriş",
    "📐 Eliptik Eğriler",
    "➕ Nokta Toplama",
    "✖️  Skaler Çarpım",
    "🔢 Sonlu Alan",
    "⚡ Double-and-Add",
    "🔑 Anahtar Üretimi",
    "🤝 ECDH Anahtar Değişimi",
    "✍️  ECDSA Dijital İmza",
    "🛡️  Güvenlik Testi",
    "📊 ECC vs RSA",
    "📨 Tam Senaryo",
    "💬 Canlı Sohbet",
]

with st.sidebar:
    st.title("ECC Navigasyon")
    page = st.radio("Bölüm seç:", PAGES, label_visibility="collapsed")
    st.divider()

# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Giriş
# ══════════════════════════════════════════════════════════════════════════════
if page == PAGES[0]:
    st.title("🔐 Eliptik Eğri Kriptografisi (ECC)")


    st.divider()
    col1, col2, col3 = st.columns(3)
    col1.metric("secp256k1 p boyutu", "256 bit", "~10⁷⁷ olasılık")
    col2.metric("RSA denk güvenlik", "3072 bit", "12× daha büyük")
    col3.metric("Double-and-Add adımı", "O(log k)", "Naif: O(k)")



# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Eliptik Eğriler
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[1]:
    st.title("📐 Eliptik Eğriler")
    st.caption("💡 ECC'nin üzerine inşa edildiği matematiksel yapıyı tanımak için.")
    st.markdown("Genel form: **y² = x³ + ax + b**")

    col1, col2 = st.columns([1, 2])
    with col1:
        a_val = st.slider("a parametresi", -5, 5, 0)
        b_val = st.slider("b parametresi", -5, 7, 7)
        disc = 4 * a_val ** 3 + 27 * b_val ** 2
        if disc == 0:
            st.error("⚠️ Tekil eğri! (discriminant = 0)\nKriptografide kullanılamaz.")
        else:
            st.success(f"Geçerli eğri ✓  (discriminant = {disc})")
        st.divider()
        st.markdown("**Hazır eğriler:**")
        if st.button("secp256k1 (Bitcoin)  a=0, b=7"): a_val, b_val = 0, 7
        if st.button("NIST P-256  a=−3, b=41058..."): a_val, b_val = -3, 3

    with col2:
        fig, axes = plt.subplots(1, 2, figsize=(11, 5))
        # Seçili eğri
        ax = axes[0]
        draw_real_curve(ax, a_val, b_val)
        ax.set_title(f"y² = x³ + {a_val}x + {b_val}", fontweight="bold")
        ax.set_xlabel("x"); ax.set_ylabel("y")

        # 3 klasik eğri
        ax = axes[1]
        for (ac, bc, lbl, col) in [(0, 7, "secp256k1", "blue"),
                                    (-3, 3, "a=−3,b=3", "green"),
                                    (0, -1, "a=0,b=−1", "orange")]:
            x = np.linspace(-3, 4, 2000)
            ysq = x ** 3 + ac * x + bc
            m = ysq >= 0
            ax.plot(x[m],  np.sqrt(ysq[m]),  color=col, lw=1.8, label=lbl)
            ax.plot(x[m], -np.sqrt(ysq[m]),  color=col, lw=1.8)
        ax.axhline(0, color="gray", lw=0.7, ls="--")
        ax.axvline(0, color="gray", lw=0.7, ls="--")
        ax.set_xlim(-3, 4); ax.set_ylim(-6, 6)
        ax.grid(True, alpha=0.3); ax.legend(fontsize=9)
        ax.set_title("Farklı a, b değerleri", fontweight="bold")
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Nokta Toplama
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[2]:
    st.title("➕ Nokta Toplama")
    st.caption("💡 Kriptografinin temel işlemi olan nokta toplamayı geometrik olarak kavramak için.")
    st.markdown("""
    **P + Q = R** işleminin geometrik anlamı:
    1. P ve Q'dan geçen doğruyu çiz
    2. Eğriyi 3. kez kestiği noktayı bul (R')
    3. R' noktasını x eksenine göre yansıt → **R = P + Q**

    **Formül:**
    ```
    λ = (y₂ − y₁) / (x₂ − x₁)
    x₃ = λ² − x₁ − x₂
    y₃ = λ(x₁ − x₃) − y₁
    ```
    """)

    col1, col2 = st.columns([1, 2])
    with col1:
        mode = st.radio("İşlem türü", ["P + Q (farklı noktalar)", "2P (nokta katlama)"])
        px = st.slider("P.x", -2.0, 2.0, -1.0, 0.1)
        curve_r = EllipticCurveReal(a=0, b=7)
        py_sq = px ** 3 + 7
        if py_sq < 0:
            st.warning("Bu x değeri eğri üzerinde değil.")
        else:
            py = np.sqrt(py_sq)
            P = (px, py)
            if "farklı" in mode:
                qx = st.slider("Q.x", -1.0, 3.0, 2.0, 0.1)
                qy_sq = qx ** 3 + 7
                if qy_sq >= 0:
                    Q = (qx, np.sqrt(qy_sq))
                    R = curve_r.add(P, Q)
                else:
                    st.warning("Q.x eğri üzerinde değil.")
                    Q = R = None
            else:
                Q = P
                R = curve_r.double(P)

            if R:
                st.info(f"P = ({P[0]:.3f}, {P[1]:.3f})\nQ = ({Q[0]:.3f}, {Q[1]:.3f})\nR = ({R[0]:.3f}, {R[1]:.3f})")

    with col2:
        if py_sq >= 0 and R:
            fig, ax = plt.subplots(figsize=(8, 6))
            draw_real_curve(ax, 0, 7)
            ax.set_title("y² = x³ + 7  (secp256k1)", fontweight="bold")

            R_prime = (R[0], -R[1])
            if "farklı" in mode and Q != P:
                lam = (Q[1] - P[1]) / (Q[0] - P[0])
                x_l = np.linspace(min(P[0], Q[0], R[0]) - 0.5, max(P[0], Q[0], R[0]) + 0.5, 200)
            else:
                lam = (3 * P[0] ** 2) / (2 * P[1])
                x_l = np.linspace(P[0] - 2, P[0] + 3, 200)
            ax.plot(x_l, lam * (x_l - P[0]) + P[1], "orange", lw=1.5, ls="--", label="Kesişen doğru")
            ax.annotate("", xy=R, xytext=R_prime,
                        arrowprops=dict(arrowstyle="<->", color="green", lw=1.8))
            for pt, name, col in [(P, "P", "red"), (Q, "Q", "purple"),
                                   (R_prime, "R'", "orange"), (R, "R=P+Q", "green")]:
                ax.scatter(*pt, s=90, color=col, zorder=5)
                ax.annotate(name, pt, xytext=(8, 5), textcoords="offset points",
                            fontsize=10, color=col, fontweight="bold")
            ax.legend(fontsize=9)
            plt.tight_layout()
            st.pyplot(fig)
            plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Skaler Çarpım
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[3]:
    st.title("✖️ Skaler Çarpım: k × P")
    st.caption("💡 Anahtar üretiminin ve şifrelemenin dayandığı tek yönlü işlemi görmek için.")
    st.markdown("""
    **k×P** = P'yi k kez kendi kendine toplamak.

    Bu işlem **tek yönlüdür** (trapdoor):
    - k ve P biliniyorsa → **k×P kolayca hesaplanır**
    - k×P ve P biliniyorsa → **k bulmak imkânsız** (Ayrık Logaritma Problemi)
    """)

    k_max = st.slider("Kaç noktaya kadar göster? (k)", 2, 12, 8)
    curve_r = EllipticCurveReal(a=0, b=7)
    P0 = (1, np.sqrt(8))

    points = {}
    cur = None
    for i in range(1, k_max + 1):
        cur = curve_r.add(cur, P0)
        if cur: points[i] = cur

    col1, col2 = st.columns([1, 2])
    with col1:
        st.markdown("**Hesaplanan noktalar:**")
        for k, pt in points.items():
            st.write(f"`{k}P` = ({pt[0]:.3f}, {pt[1]:.3f})")

    with col2:
        fig, ax = plt.subplots(figsize=(9, 7))
        all_xs = [pt[0] for pt in points.values()]
        all_ys = [pt[1] for pt in points.values()]
        pad_x = max(1.5, (max(all_xs) - min(all_xs)) * 0.2)
        pad_y = max(2.0, (max(all_ys) - min(all_ys)) * 0.2)
        xlim = (min(-3, min(all_xs) - pad_x), max(5, max(all_xs) + pad_x))
        ylim = (min(-8, min(all_ys) - pad_y), max(8,  max(all_ys) + pad_y))
        draw_real_curve(ax, 0, 7, xlim=xlim, ylim=ylim)
        ax.set_title(f"Skaler Çarpım: 1P … {k_max}P", fontweight="bold")

        colors = plt.cm.plasma(np.linspace(0.1, 0.9, len(points)))
        for i, (k, pt) in enumerate(points.items()):
            ax.scatter(*pt, s=130, color=colors[i], zorder=5)
            ax.annotate(f"{k}P", pt, xytext=(8, 5), textcoords="offset points",
                        fontsize=10, color=colors[i], fontweight="bold")
        pts_list = list(points.values())
        for i in range(len(pts_list) - 1):
            ax.annotate("", xy=pts_list[i + 1], xytext=pts_list[i],
                        arrowprops=dict(arrowstyle="->", color="gray", lw=1.0, alpha=0.5))
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)



# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Sonlu Alan
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[4]:
    st.title("🔢 Sonlu Alan (Finite Field)")
    st.caption("💡 Gerçek kriptografinin neden sonsuz sayılar yerine mod p kullandığını anlamak için.")
    st.markdown("""
    Gerçek ECC, **mod p** (asal sayı) aritmetiği kullanır:

    **y² ≡ x³ + ax + b  (mod p)**

    - Tüm değerler `[0, p−1]` arasında kalır
    - Bölme işlemi → **modüler ters** ile yapılır
    - Sonuç: Sonsuz sayı yerine **kapalı ve güvenli bir sistem**
    """)

    col1, col2 = st.columns([1, 2])
    with col1:
        p_val = st.select_slider("Asal sayı p", options=[17, 23, 31, 41, 53, 71, 97], value=97)
        a_f = st.slider("a", -5, 5, 2)
        b_f = st.slider("b", 1, 10, 3)

    fc = EllipticCurveFinite(a=a_f, b=b_f, p=p_val)
    pts = fc.get_all_points()

    with col1:
        st.metric("Eğri üzerindeki nokta sayısı", len(pts))
        st.caption("(+ sonsuz nokta O)")

    with col2:
        fig, axes = plt.subplots(1, 2, figsize=(12, 5))
        ax = axes[0]
        xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
        ax.scatter(xs, ys, s=20, color="steelblue", alpha=0.85)
        ax.set_title(f"y² ≡ x³ + {a_f}x + {b_f}  (mod {p_val})", fontweight="bold")
        ax.set_xlim(-1, p_val); ax.set_ylim(-1, p_val)
        ax.grid(True, alpha=0.3)
        ax.set_xlabel("x"); ax.set_ylabel("y")

        ax = axes[1]
        primes = [17, 31, 53, 97]
        colors2 = ["red", "orange", "green", "blue"]
        for pr, col in zip(primes, colors2):
            c2 = EllipticCurveFinite(a=a_f, b=b_f, p=pr)
            p2 = c2.get_all_points()
            ax.scatter([pt[0] / pr for pt in p2], [pt[1] / pr for pt in p2],
                       s=18, color=col, alpha=0.6, label=f"p={pr} ({len(p2)} nokta)")
        ax.set_title("Farklı p değerlerinde dağılım (normalize)", fontweight="bold")
        ax.set_xlabel("x/p"); ax.set_ylabel("y/p")
        ax.legend(fontsize=9); ax.grid(True, alpha=0.3)

        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Double-and-Add
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[5]:
    st.title("⚡ Double-and-Add Algoritması")
    st.caption("💡 Büyük sayılarla hesabın neden pratikte mümkün olduğunu göstermek için.")
    st.markdown("""
    Büyük k için k×P'yi **O(log₂ k)** adımda hesapla:

    ```
    Algoritma:
      result = O (sonsuz nokta)
      for bit in bin(k):           # yüksekten düşüğe
          result = 2 × result      # Double
          if bit == 1:
              result = result + P  # Add
    ```
    """)

    k_demo = st.number_input("k değeri gir:", min_value=2, max_value=10000, value=100)

    binary = bin(k_demo)[2:]
    st.markdown(f"**{k_demo}** → ikili: `{binary}` ({len(binary)} bit)")

    rows = []
    result = 0
    for i, bit in enumerate(binary):
        if i == 0:
            result = 1
            rows.append({"Adım": i + 1, "İşlem": "Başlangıç", "Sonuç": f"1×P", "Bit": bit})
        else:
            result *= 2
            op = "Double"
            if bit == "1":
                result += 1
                op = "Double + Add"
            rows.append({"Adım": i + 1, "İşlem": op, "Sonuç": f"{result}×P", "Bit": bit})

    st.dataframe(rows, use_container_width=True)

    naive = k_demo - 1
    daa   = len(binary) + binary.count("1") - 1
    col1, col2, col3 = st.columns(3)
    col1.metric("Naif toplama sayısı", naive)
    col2.metric("Double-and-Add adımı", daa)
    col3.metric("Tasarruf", f"{naive - daa} işlem", f"−{100*(naive-daa)/naive:.1f}%")

    # Karmaşıklık grafiği
    ks = range(2, 501)
    naive_ops = [k - 1 for k in ks]
    daa_ops = [len(bin(k)) + bin(k).count("1") - 2 for k in ks]

    fig, ax = plt.subplots(figsize=(9, 4))
    ax.plot(ks, naive_ops, "r-", lw=1.5, label="Naif: O(k)", alpha=0.7)
    ax.plot(ks, daa_ops, "b-", lw=2, label="Double-and-Add: O(log k)")
    ax.fill_between(ks, daa_ops, naive_ops, alpha=0.1, color="green")
    ax.set_xlabel("k"); ax.set_ylabel("İşlem Sayısı")
    ax.set_title("Karmaşıklık Karşılaştırması", fontweight="bold")
    ax.legend(); ax.grid(True, alpha=0.3)
    plt.tight_layout()
    st.pyplot(fig)
    plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Anahtar Üretimi
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[6]:
    st.title("🔑 Anahtar Üretimi")
    st.caption("💡 Özel ve açık anahtar arasındaki tek yönlü ilişkiyi somutlaştırmak için.")
    st.markdown("""
    ```
    Özel Anahtar (d) : Rastgele seçilen büyük sayı  [1, n−1]
    Açık  Anahtar (Q) : Q = d × G
    ```
    - **d → Q** hesabı: kolay (Double-and-Add, ~256 adım)
    - **Q → d** hesabı: imkânsız (Ayrık Logaritma Problemi)
    """)

    if st.button("🎲 Yeni Anahtar Çifti Üret", type="primary"):
        st.session_state["keypair"] = generate_keypair()

    if "keypair" not in st.session_state:
        st.session_state["keypair"] = generate_keypair()

    d, Q = st.session_state["keypair"]

    col1, col2 = st.columns(2)
    with col1:
        st.subheader("Özel Anahtar (d)")
        st.code(hex(d), language="text")
        st.caption(f"{d.bit_length()} bit")
    with col2:
        st.subheader("Açık Anahtar Q = (x, y)")
        st.code(f"x = {hex(Q[0])}\ny = {hex(Q[1])}", language="text")

    # Tek yönlü görsel
    fig, ax = plt.subplots(figsize=(10, 2.5))
    ax.axis("off")
    boxes = [
        (0.1, "Rastgele d\n(Özel Anahtar)\n256-bit", "#ffcccc"),
        (0.43, "d × G\n(Double-and-Add\n~256 adım)", "#fff3cc"),
        (0.77, "Q = (x, y)\n(Açık Anahtar)\nEğri noktası", "#ccffcc"),
    ]
    for xp, txt, col in boxes:
        ax.text(xp + 0.1, 0.55, txt, ha="center", va="center",
                transform=ax.transAxes, fontsize=10,
                bbox=dict(boxstyle="round,pad=0.4", facecolor=col, edgecolor="gray", lw=1.5))
    for x1, x2 in [(0.28, 0.42), (0.62, 0.76)]:
        ax.annotate("", xy=(x2, 0.55), xytext=(x1, 0.55),
                    xycoords="axes fraction", textcoords="axes fraction",
                    arrowprops=dict(arrowstyle="->", color="green", lw=2))
    ax.annotate("", xy=(0.13, 0.12), xytext=(0.87, 0.12),
                xycoords="axes fraction", textcoords="axes fraction",
                arrowprops=dict(arrowstyle="->", color="red", lw=2, linestyle="dashed"))
    ax.text(0.5, 0.03, "Geri dönmek MÜMKÜN DEĞİL  (Ayrık Logaritma Problemi)",
            ha="center", va="center", transform=ax.transAxes,
            fontsize=9, color="red", style="italic")
    plt.tight_layout()
    st.pyplot(fig)
    plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: ECDH
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[7]:
    st.title("🤝 ECDH — Anahtar Değişimi")
    st.caption("💡 İki tarafın güvensiz bir kanalda ortak sır nasıl oluşturduğunu göstermek için.")
    st.markdown("""
    Alice ve Bob **güvensiz** bir kanal üzerinden **ortak gizli** oluşturur:

    ```
    Alice: S = d_A × Q_B = d_A × (d_B × G)
    Bob  : S = d_B × Q_A = d_B × (d_A × G)
    ─────────────────────────────────────────
    Her ikisi de aynı S noktasına ulaşır!
    ```
    """)

    if st.button("🔄 Yeni Anahtar Çiftleri Üret", type="primary"):
        st.session_state["ecdh_alice"] = generate_keypair()
        st.session_state["ecdh_bob"]   = generate_keypair()

    if "ecdh_alice" not in st.session_state:
        st.session_state["ecdh_alice"] = generate_keypair()
        st.session_state["ecdh_bob"]   = generate_keypair()

    a_priv, a_pub = st.session_state["ecdh_alice"]
    b_priv, b_pub = st.session_state["ecdh_bob"]

    shared_pt_a = SECP256K1.scalar_mult(a_priv, b_pub)
    shared_pt_b = SECP256K1.scalar_mult(b_priv, a_pub)
    match = shared_pt_a == shared_pt_b

    col1, col2, col3 = st.columns(3)
    with col1:
        st.subheader("👩 Alice")
        st.write("**Özel:** `d_A`")
        st.code(hex(a_priv)[:30] + "...", language="text")
        st.write("**Açık:** `Q_A = d_A × G`")
        st.code(hex(a_pub[0])[:20] + "...", language="text")
    with col2:
        st.subheader("🌐 Ortak Sır")
        st.write("Alice hesaplar: `d_A × Q_B`")
        st.write("Bob hesaplar: `d_B × Q_A`")
        if match:
            st.success("✅ Eşleşiyor!")
        else:
            st.error("❌ Eşleşmiyor!")
        st.code(hex(shared_pt_a[0])[:25] + "...", language="text")
    with col3:
        st.subheader("👨 Bob")
        st.write("**Özel:** `d_B`")
        st.code(hex(b_priv)[:30] + "...", language="text")
        st.write("**Açık:** `Q_B = d_B × G`")
        st.code(hex(b_pub[0])[:20] + "...", language="text")

    # Akış diyagramı
    fig, ax = plt.subplots(figsize=(12, 6))
    ax.axis("off"); ax.set_xlim(0, 10); ax.set_ylim(0, 9)

    def rbox(ax, x, y, txt, col, w=2.2, h=0.8):
        r = mpatches.FancyBboxPatch((x - w / 2, y - h / 2), w, h,
            boxstyle="round,pad=0.1", facecolor=col, edgecolor="gray", lw=1.4)
        ax.add_patch(r)
        ax.text(x, y, txt, ha="center", va="center", fontsize=9, fontweight="bold")

    def rarr(ax, x1, y1, x2, y2, lbl="", col="black"):
        ax.annotate("", xy=(x2, y2), xytext=(x1, y1),
                    arrowprops=dict(arrowstyle="->", color=col, lw=1.8))
        if lbl:
            ax.text((x1 + x2) / 2, (y1 + y2) / 2 + 0.2, lbl,
                    ha="center", fontsize=8, color=col, style="italic")

    rbox(ax, 2, 8, "ALICE", "#ffcccc", w=2.5)
    rbox(ax, 8, 8, "BOB",   "#cce5ff", w=2.5)
    rbox(ax, 2, 6.5, "d_A (özel anahtar)", "#ff9999")
    rbox(ax, 8, 6.5, "d_B (özel anahtar)", "#6699ff")
    rbox(ax, 2, 5, "Q_A = d_A × G\n(açık anahtar)", "#ffdddd", w=2.6, h=0.9)
    rbox(ax, 8, 5, "Q_B = d_B × G\n(açık anahtar)", "#ddeeff", w=2.6, h=0.9)
    rarr(ax, 3.4, 5.0, 6.6, 5.0, "Q_A → (herkese açık)", "green")
    rarr(ax, 6.6, 4.5, 3.4, 4.5, "← Q_B (herkese açık)", "green")
    rbox(ax, 2, 3.2, "S = d_A × Q_B", "#ffe0b3")
    rbox(ax, 8, 3.2, "S = d_B × Q_A", "#b3d9ff")
    rarr(ax, 2, 4.5, 2, 3.6, col="gray")
    rarr(ax, 8, 4.5, 8, 3.6, col="gray")
    rbox(ax, 5, 1.7, "S = d_A × d_B × G\n(Ortak Gizli Anahtar)", "#ccffcc", w=3.8, h=1.0)
    rarr(ax, 2, 2.8, 3.2, 2.1, col="purple")
    rarr(ax, 8, 2.8, 6.8, 2.1, col="purple")
    rbox(ax, 5, 6.2, "Gözlemci\nGörür: G, Q_A, Q_B\nBilemez: d_A, d_B, S", "#f0f0f0", w=3.0, h=1.2)
    ax.set_title("ECDH Anahtar Değişimi", fontsize=13, fontweight="bold", y=0.98)
    plt.tight_layout()
    st.pyplot(fig)
    plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: ECDSA
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[8]:
    st.title("✍️ ECDSA — Dijital İmza")
    st.caption("💡 Bir mesajın kimin tarafından yazıldığını ve değiştirilmediğini nasıl ispatlayacağımızı göstermek için.")

    tab1, tab2 = st.tabs(["📝 İmzalama", "🔍 Doğrulama"])

    with tab1:
        st.markdown("""
        **İmzalama adımları:**
        ```
        1. e = SHA256(mesaj)
        2. k = rastgele seç  [1, n−1]
        3. R = k × G  →  r = R.x mod n
        4. s = k⁻¹ × (e + r × d)  mod n
        İmza = (r, s)
        ```
        """)

        if "ecdsa_key" not in st.session_state:
            st.session_state["ecdsa_key"] = generate_keypair()

        d_sign, Q_sign = st.session_state["ecdsa_key"]

        if st.button("🎲 Yeni Anahtar Üret"):
            st.session_state["ecdsa_key"] = generate_keypair()
            st.rerun()

        msg_input = st.text_input("İmzalanacak mesaj:", value="Merhaba, bu ECC ile imzalandı!")

        if st.button("✍️ İmzala", type="primary"):
            msg_bytes = msg_input.encode()
            sig = ecdsa_sign(msg_bytes, d_sign)
            st.session_state["last_sig"] = sig
            st.session_state["last_msg"] = msg_input
            st.session_state["last_pub"] = Q_sign

        if "last_sig" in st.session_state:
            sig = st.session_state["last_sig"]
            col1, col2 = st.columns(2)
            col1.metric("r", hex(sig[0])[:20] + "...")
            col2.metric("s", hex(sig[1])[:20] + "...")
            st.code(f"r = {hex(sig[0])}\ns = {hex(sig[1])}", language="text")

    with tab2:
        st.markdown("""
        **Doğrulama adımları:**
        ```
        1. e = SHA256(mesaj)
        2. w = s⁻¹  mod n
        3. u₁ = e·w  mod n,  u₂ = r·w  mod n
        4. Nokta = u₁×G + u₂×Q
        5. Nokta.x mod n == r  →  GEÇERLİ
        ```
        """)

        if "last_sig" in st.session_state:
            verify_msg = st.text_input("Doğrulanacak mesaj:", value=st.session_state["last_msg"])
            if st.button("🔍 Doğrula", type="primary"):
                ok = ecdsa_verify(verify_msg.encode(), st.session_state["last_sig"],
                                  st.session_state["last_pub"])
                if ok:
                    st.success("✅ İmza GEÇERLİ — mesaj değiştirilmemiş!")
                else:
                    st.error("❌ İmza GEÇERSİZ — mesaj değiştirilmiş veya yanlış anahtar!")
        else:
            st.info("Önce İmzalama sekmesinden bir imza oluşturun.")



# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Güvenlik Testi
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[9]:
    st.title("🛡️ Güvenlik Testi")
    st.caption("💡 İmzanın manipülasyona karşı gerçekten dayanıklı olduğunu test etmek için.")
    st.markdown("Farklı senaryolarda ECDSA doğrulama davranışını test et:")

    if "sec_key" not in st.session_state:
        st.session_state["sec_key"]  = generate_keypair()
        st.session_state["sec_key2"] = generate_keypair()

    d_s, Q_s   = st.session_state["sec_key"]
    _, Q_other = st.session_state["sec_key2"]

    original = st.text_input("Orijinal mesaj:", "Banka transferi: 100 TL")

    if st.button("🔏 Orijinal mesajı imzala", type="primary"):
        sig = ecdsa_sign(original.encode(), d_s)
        st.session_state["sec_sig"] = sig
        st.session_state["sec_orig"] = original

    if "sec_sig" in st.session_state:
        sig = st.session_state["sec_sig"]
        st.subheader("Test Sonuçları")

        modified = st.text_input("Değiştirilmiş mesaj:", "Banka transferi: 10000 TL")

        tests = [
            ("Orijinal mesaj + Doğru anahtar",     original,  Q_s,     True),
            ("Değiştirilmiş mesaj + Doğru anahtar", modified,  Q_s,     False),
            ("Orijinal mesaj + Yanlış anahtar",    original,  Q_other, False),
        ]

        cols = st.columns(3)
        for col, (desc, msg, pub, expected) in zip(cols, tests):
            result = ecdsa_verify(msg.encode(), sig, pub)
            icon = "✅" if result else "❌"
            status = "GEÇERLİ" if result else "GEÇERSİZ"
            beklenen = "✓ Beklenen" if result == expected else "⚠️ Beklenmeyen"
            col.metric(desc, f"{icon} {status}", beklenen)

        # Görsel
        fig, ax = plt.subplots(figsize=(10, 3.5))
        ax.axis("off")
        colors_bar = []
        labels_bar = []
        statuses   = []
        for desc, msg, pub, expected in tests:
            r = ecdsa_verify(msg.encode(), sig, pub)
            colors_bar.append("#2ecc71" if r else "#e74c3c")
            labels_bar.append(desc)
            statuses.append("GEÇERLİ" if r else "GEÇERSİZ")

        ax2 = fig.add_axes([0.05, 0.15, 0.9, 0.7])
        bars = ax2.barh(labels_bar, [1, 1, 1], color=colors_bar, height=0.4)
        for bar, txt in zip(bars, statuses):
            ax2.text(0.5, bar.get_y() + bar.get_height() / 2, txt,
                     ha="center", va="center", fontsize=13, fontweight="bold", color="white")
        ax2.set_xlim(0, 1); ax2.axis("off")
        plt.suptitle("ECDSA Güvenlik Testi", fontsize=12, fontweight="bold")
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)
    else:
        st.info("Önce mesajı imzalayın.")


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: ECC vs RSA
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[10]:
    st.title("📊 ECC vs RSA Karşılaştırması")
    st.caption("💡 ECC'nin neden modern sistemlerde RSA'ya tercih edildiğini göstermek için.")
    st.markdown("Aynı güvenlik seviyesi için gereken anahtar boyutları:")

    levels = [80, 112, 128, 192, 256]
    ecc_ks = [160, 224, 256, 384, 521]
    rsa_ks = [1024, 2048, 3072, 7680, 15360]

    import pandas as pd
    df = pd.DataFrame({
        "Güvenlik (bit)": levels,
        "ECC Anahtar (bit)": ecc_ks,
        "RSA Anahtar (bit)": rsa_ks,
        "RSA/ECC Oranı": [f"{r/e:.1f}×" for e, r in zip(ecc_ks, rsa_ks)],
    })
    st.dataframe(df, use_container_width=True, hide_index=True)

    fig, axes = plt.subplots(1, 2, figsize=(13, 5))

    ax = axes[0]
    x = range(len(levels))
    w = 0.35
    b1 = ax.bar([i - w/2 for i in x], ecc_ks, w, label="ECC", color="steelblue")
    b2 = ax.bar([i + w/2 for i in x], rsa_ks, w, label="RSA", color="tomato")
    ax.set_xticks(list(x))
    ax.set_xticklabels([f"{s}-bit" for s in levels])
    ax.set_ylabel("Anahtar Boyutu (bit)")
    ax.set_title("Anahtar Boyutları", fontweight="bold")
    ax.legend(); ax.grid(True, alpha=0.3, axis="y")
    for bar in b1:
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 80,
                str(int(bar.get_height())), ha="center", fontsize=8, color="steelblue")
    for bar in b2:
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 80,
                str(int(bar.get_height())), ha="center", fontsize=8, color="tomato")

    ax = axes[1]
    ax.axis("off")
    table_data = [
        ["Özellik",            "ECC",              "RSA"],
        ["128-bit güvenlik",   "256-bit anahtar",  "3072-bit anahtar"],
        ["Anahtar üretimi",    "Hızlı",            "Yavaş"],
        ["İmzalama",           "Çok hızlı",        "Hızlı"],
        ["Doğrulama",          "Hızlı",            "Çok hızlı"],
        ["Bandwidth",          "Düşük",            "Yüksek"],
        ["Kullanım",           "TLS, Bitcoin,\nSmart card", "TLS, SSH, E-posta"],
    ]
    tbl = ax.table(cellText=table_data[1:], colLabels=table_data[0],
                   loc="center", cellLoc="center")
    tbl.auto_set_font_size(False); tbl.set_fontsize(9); tbl.scale(1.2, 1.6)
    for (row, col), cell in tbl.get_celld().items():
        if row == 0:
            cell.set_facecolor("#2c3e50"); cell.set_text_props(color="white", fontweight="bold")
        elif col == 1: cell.set_facecolor("#d5e8d4")
        elif col == 2: cell.set_facecolor("#fff2cc")
    ax.set_title("Karşılaştırma Tablosu", fontweight="bold", pad=10)

    plt.tight_layout()
    st.pyplot(fig)
    plt.close(fig)


# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Tam Senaryo
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[11]:
    st.title("📨 Tam Senaryo: Alice → Bob")
    st.caption("💡 Şifrelemenin nasıl adım adım inşa edildiğini simüle ederek görmek için.")

    # ── session state init ─────────────────────────────────────────────────────
    if "scen_step" not in st.session_state:
        st.session_state["scen_step"] = 0

    TOTAL_STEPS = 7
    step = st.session_state["scen_step"]

    # ── helper: Double-and-Add trace table ─────────────────────────────────────
    def daa_trace(k, max_show=14):
        binary = bin(k)[2:]
        rows = []
        acc = 0
        ellipsis_added = False
        for i, bit in enumerate(binary):
            if i == 0:
                acc = 1
                op = "Başlangıç (bit=1)"
            else:
                acc = acc * 2
                if bit == "1":
                    acc += 1
                    op = "Double + Add  (bit=1)"
                else:
                    op = "Double        (bit=0)"
            in_head = i < max_show
            in_tail = i >= len(binary) - 2
            if in_head or in_tail:
                acc_str = (f"{acc}×G" if acc < 10000
                           else f"{hex(acc)[:10]}...×G")
                rows.append({"Adım": i + 1, "Bit": bit, "İşlem": op,
                             "Akümülatör": acc_str})
            elif not ellipsis_added:
                rows.append({"Adım": "⋮", "Bit": "⋮",
                             "İşlem": f"← {len(binary) - max_show - 2} adım daha →",
                             "Akümülatör": "⋮"})
                ellipsis_added = True
        return rows

    # ── progress indicator ─────────────────────────────────────────────────────
    step_labels = [
        "Hazırlık", "Alice Anahtar", "Bob Anahtar",
        "ECDH Ortak Sır", "Şifrele + İmzala", "📡 İletim", "Bob: Çöz + Doğrula",
    ]
    prog_cols = st.columns(TOTAL_STEPS)
    for i, (col, lbl) in enumerate(zip(prog_cols, step_labels)):
        if i < step:
            col.markdown(f"<div style='text-align:center;color:#2ecc71;font-size:11px'>✓ {lbl}</div>",
                         unsafe_allow_html=True)
        elif i == step:
            col.markdown(f"<div style='text-align:center;color:#2980b9;font-weight:bold;font-size:11px'>▶ {lbl}</div>",
                         unsafe_allow_html=True)
        else:
            col.markdown(f"<div style='text-align:center;color:#aaa;font-size:11px'>○ {lbl}</div>",
                         unsafe_allow_html=True)
    st.progress(step / TOTAL_STEPS)
    st.divider()

    # ── nav buttons ────────────────────────────────────────────────────────────
    def nav_buttons(allow_next=True, next_label="İleri ▶"):
        c1, c2, c3 = st.columns([1, 4, 1])
        with c1:
            if step > 0 and st.button("◀ Geri"):
                st.session_state["scen_step"] -= 1
                st.rerun()
        with c3:
            if allow_next and st.button(next_label, type="primary"):
                st.session_state["scen_step"] += 1
                st.rerun()

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 0 — Setup
    # ══════════════════════════════════════════════════════════════════════════
    if step == 0:
        st.subheader("Adım 0 — Hazırlık")
        st.markdown("Alice'ten Bob'a güvenli mesaj gönderimini **adım adım** simüle eder: anahtar üretimi → ECDH → şifrele + imzala → ilet → çöz + doğrula.")

        msg_input = st.text_input("Alice'in göndereceği mesaj:", "Merhaba Bob! Bu tamamen gizli.")
        if st.button("🚀 Simülasyonu Başlat", type="primary"):
            # Pre-compute everything once and store
            a_priv, a_pub = generate_keypair()
            b_priv, b_pub = generate_keypair()
            shared_pt_a   = SECP256K1.scalar_mult(a_priv, b_pub)
            shared_pt_b   = SECP256K1.scalar_mult(b_priv, a_pub)
            shared_secret = shared_pt_a[0]
            msg_bytes     = msg_input.encode()
            encrypted     = xor_encrypt(msg_bytes, shared_secret)
            sig           = ecdsa_sign(msg_bytes, a_priv)
            e_hash        = hash_message(msg_bytes)
            n             = SECP256K1.n
            # re-derive k for display (sign again with fixed seed for traceability)
            k_show = random.randint(1, n - 1)
            R_show = SECP256K1.scalar_mult(k_show, SECP256K1.G)
            decrypted     = xor_encrypt(encrypted, shared_pt_b[0])
            sig_ok        = ecdsa_verify(decrypted, sig, a_pub)

            st.session_state["scen_data"] = {
                "msg": msg_input,
                "msg_bytes": msg_bytes,
                "a_priv": a_priv, "a_pub": a_pub,
                "b_priv": b_priv, "b_pub": b_pub,
                "shared_secret": shared_secret,
                "shared_pt_b": shared_pt_b,
                "encrypted": encrypted,
                "sig": sig,
                "e_hash": e_hash,
                "k_show": k_show,
                "R_show": R_show,
                "decrypted": decrypted,
                "sig_ok": sig_ok,
            }
            st.session_state["scen_step"] = 1
            st.rerun()

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 1 — Alice key generation
    # ══════════════════════════════════════════════════════════════════════════
    elif step == 1:
        d = st.session_state["scen_data"]
        st.subheader("Adım 1 — Alice: Anahtar Çifti Üretimi")

        st.markdown("""
        **Özel anahtar** `d_A`: `[1, n−1]` aralığından rastgele seçilir.
        **Açık anahtar** `Q_A`: Double-and-Add algoritmasıyla `Q_A = d_A × G` hesaplanır.
        """)

        col1, col2 = st.columns(2)
        with col1:
            st.markdown("#### Özel Anahtar `d_A`")
            st.code(hex(d["a_priv"]), language="text")
            binary_d = bin(d["a_priv"])[2:]
            st.caption(f"{len(binary_d)} bit — ikili: `{binary_d[:16]}...{binary_d[-8:]}`")

        with col2:
            st.markdown("#### Açık Anahtar `Q_A = d_A × G`")
            st.code(f"x = {hex(d['a_pub'][0])[:34]}...\ny = {hex(d['a_pub'][1])[:34]}...",
                    language="text")
            st.caption("Eğri üzerinde bir nokta — herkese açık paylaşılır")

        nav_buttons(next_label="Bob'a geç ▶")

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 2 — Bob key generation
    # ══════════════════════════════════════════════════════════════════════════
    elif step == 2:
        d = st.session_state["scen_data"]
        st.subheader("Adım 2 — Bob: Anahtar Çifti Üretimi")
        st.markdown("Bob da aynı süreci **bağımsız** olarak yapar:")

        col1, col2 = st.columns(2)
        with col1:
            st.markdown("#### Özel Anahtar `d_B`")
            st.code(hex(d["b_priv"]), language="text")
            binary_b = bin(d["b_priv"])[2:]
            st.caption(f"{len(binary_b)} bit — ikili: `{binary_b[:16]}...{binary_b[-8:]}`")

        with col2:
            st.markdown("#### Açık Anahtar `Q_B = d_B × G`")
            st.code(f"x = {hex(d['b_pub'][0])[:34]}...\ny = {hex(d['b_pub'][1])[:34]}...",
                    language="text")

        st.info("Özel anahtarlar (`d_A`, `d_B`) **hiç kimseyle paylaşılmaz** — yalnızca açık anahtarlar paylaşılır.")
        nav_buttons(next_label="ECDH'ye geç ▶")

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 3 — ECDH shared secret
    # ══════════════════════════════════════════════════════════════════════════
    elif step == 3:
        d = st.session_state["scen_data"]
        st.subheader("Adım 3 — ECDH: Ortak Sır Oluşturma")

        st.markdown("""
        Alice ve Bob **karşılıklı açık anahtarları** kullanarak, **aynı ortak sırrı** bağımsız hesaplar.
        Gözlemci sadece `Q_A`, `Q_B`, ve `G`'yi bilir — `d_A` veya `d_B`'yi bilemez.
        """)

        col1, col2, col3 = st.columns(3)

        with col1:
            st.markdown("#### 👩 Alice hesaplar")
            st.markdown("`S_A = d_A × Q_B`")
            st.markdown("Alice kendi özel anahtarıyla Bob'un açık anahtarını çarpar:")
            st.code(
                f"d_A = {hex(d['a_priv'])[:18]}...\n"
                f"Q_B.x = {hex(d['b_pub'][0])[:18]}...\n\n"
                f"S_A.x = {hex(d['shared_secret'])[:18]}...",
                language="text"
            )

        with col2:
            st.markdown("#### 🌐 Gözlemci görür")
            st.code(
                f"G  = (Gx, Gy)  [sabit]\n"
                f"Q_A.x = {hex(d['a_pub'][0])[:14]}...\n"
                f"Q_B.x = {hex(d['b_pub'][0])[:14]}...",
                language="text"
            )
            st.error("d_A ve d_B bilinmeden\nS hesaplanamaz!")

        with col3:
            st.markdown("#### 👨 Bob hesaplar")
            st.markdown("`S_B = d_B × Q_A`")
            st.markdown("Bob kendi özel anahtarıyla Alice'in açık anahtarını çarpar:")
            st.code(
                f"d_B = {hex(d['b_priv'])[:18]}...\n"
                f"Q_A.x = {hex(d['a_pub'][0])[:18]}...\n\n"
                f"S_B.x = {hex(d['shared_pt_b'][0])[:18]}...",
                language="text"
            )

        match = d["shared_secret"] == d["shared_pt_b"][0]
        if match:
            st.success(f"✅ S_A.x == S_B.x  →  Ortak sır eşleşiyor!\n`{hex(d['shared_secret'])[:40]}...`")
        else:
            st.error("❌ Eşleşme başarısız!")

        nav_buttons(next_label="Şifrele + İmzala ▶")

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 4 — Encrypt + Sign
    # ══════════════════════════════════════════════════════════════════════════
    elif step == 4:
        d = st.session_state["scen_data"]
        st.subheader("Adım 4 — Alice: Şifrele + İmzala")

        tab_enc, tab_sign = st.tabs(["🔒 XOR Şifreleme", "✍️ ECDSA İmzalama"])

        with tab_enc:
            st.markdown("""
            **Ortak sır → şifreleme anahtarı**
            Paylaşılan `S.x` değeri 32-byte'a dönüştürülür ve mesaj XOR ile şifrelenir.
            """)
            msg_bytes = d["msg_bytes"]
            key_bytes = d["shared_secret"].to_bytes(32, "big")
            enc_bytes = d["encrypted"]

            st.markdown("**Byte-byte şifreleme (ilk 8 byte):**")
            xor_rows = []
            for i in range(min(8, len(msg_bytes))):
                m = msg_bytes[i]
                k = key_bytes[i % 32]
                c = enc_bytes[i]
                xor_rows.append({
                    "Byte #": i,
                    "Mesaj (M)": f"{m:3d} = {m:08b}",
                    "Anahtar (K)": f"{k:3d} = {k:08b}",
                    "XOR (C=M⊕K)": f"{c:3d} = {c:08b}",
                })
            st.dataframe(xor_rows, use_container_width=True, hide_index=True)
            st.code(
                f"Orijinal mesaj : {d['msg']}\n"
                f"Şifreli (hex)  : {enc_bytes.hex()}",
                language="text"
            )
            st.caption("XOR her biti tersine çevirir — anahtar olmadan orijinal mesaj okunamaz.")

        with tab_sign:
            st.markdown("""
            **ECDSA İmzalama adımları:**

            1. `e = SHA256(mesaj)` → mesajın hash'i
            2. `k` = rastgele nonce  `[1, n−1]`
            3. `R = k × G`  → eğri üzerinde rastgele nokta (Double-and-Add!)
            4. `r = R.x mod n`
            5. `s = k⁻¹ × (e + r × d_A)  mod n`
            """)
            n = SECP256K1.n
            e_h = d["e_hash"]
            k_s = d["k_show"]
            R_s = d["R_show"]
            r_s, s_s = d["sig"]

            st.markdown("**Hesaplama izleme:**")
            sign_rows = [
                {"İşlem": "e = SHA256(mesaj)",        "Değer": hex(e_h)[:30] + "..."},
                {"İşlem": "k = rastgele nonce",       "Değer": hex(k_s)[:30] + "..."},
                {"İşlem": "R = k × G  (Double-and-Add)", "Değer": f"({hex(R_s[0])[:16]}..., {hex(R_s[1])[:16]}...)"},
                {"İşlem": "r = R.x mod n",            "Değer": hex(r_s)[:30] + "..."},
                {"İşlem": "s = k⁻¹(e + r·d_A) mod n","Değer": hex(s_s)[:30] + "..."},
                {"İşlem": "İmza σ = (r, s)",          "Değer": "✅ hazır"},
            ]
            st.dataframe(sign_rows, use_container_width=True, hide_index=True)

            with st.expander("k → R = k×G  Double-and-Add izleme (nonce noktası)"):
                trace_k = daa_trace(k_s)
                st.dataframe(trace_k, use_container_width=True, hide_index=True)
                st.caption("Bu iz, nonce k'dan R = k×G noktasının nasıl birikimli oluşturulduğunu gösterir.")

        nav_buttons(next_label="İletim ▶")

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 5 — Transmission
    # ══════════════════════════════════════════════════════════════════════════
    elif step == 5:
        d = st.session_state["scen_data"]
        st.subheader("Adım 5 — 📡 Mesaj İletimi")

        st.markdown("""
        Alice, hazırladığı paketi güvensiz kanal üzerinden Bob'a gönderir.
        Paketin içeriği:
        """)

        col1, col2 = st.columns([1, 1])
        with col1:
            st.markdown("#### 📦 Alice'in gönderdiği paket")
            st.code(
                f"┌─────────────────────────────────┐\n"
                f"│  Şifreli Mesaj (C)              │\n"
                f"│  {d['encrypted'].hex()[:28]}...  │\n"
                f"│                                 │\n"
                f"│  İmza σ = (r, s)                │\n"
                f"│  r = {hex(d['sig'][0])[:20]}...  │\n"
                f"│  s = {hex(d['sig'][1])[:20]}...  │\n"
                f"│                                 │\n"
                f"│  Alice'in Açık Anahtarı Q_A     │\n"
                f"│  x = {hex(d['a_pub'][0])[:20]}...│\n"
                f"└─────────────────────────────────┘",
                language="text"
            )

        with col2:
            st.markdown("#### 🕵️ Gözlemci ne görebilir?")
            st.warning(
                "Gözlemci paketi yakalasa bile:\n\n"
                "- `C` şifreli → orijinal mesaj okunamaz\n"
                "- `σ` imza → Alice olmadan taklit edilemez\n"
                "- `S` ortak sır → `d_A` veya `d_B` bilinmeden hesaplanamaz\n\n"
                "**ECDLP** (Ayrık Logaritma Problemi) bunu korur."
            )

        # Flow diagram
        fig, ax = plt.subplots(figsize=(13, 3.5))
        ax.axis("off"); ax.set_xlim(0, 13); ax.set_ylim(0, 4)
        flow = [
            (1.2, 2, "👩 Alice\n(C, σ, Q_A)", "#ffcccc"),
            (4.5, 2, "📡 Kanal\n(C, σ, Q_A\ngörünür)", "#fff3cc"),
            (7.8, 2, "🕵️ Gözlemci\nS bilinmiyor\norijinal okunamaz", "#ffeedd"),
            (11,  2, "👨 Bob\n(C, σ, Q_A\nalır)", "#cce5ff"),
        ]
        for x, y, txt, fc in flow:
            r = mpatches.FancyBboxPatch((x - 1.1, y - 0.9), 2.2, 1.8,
                boxstyle="round,pad=0.1", facecolor=fc, edgecolor="gray", lw=1.4)
            ax.add_patch(r)
            ax.text(x, y, txt, ha="center", va="center", fontsize=9)
        for i in range(len(flow) - 1):
            x1 = flow[i][0] + 1.1; x2 = flow[i + 1][0] - 1.1
            ax.annotate("", xy=(x2, 2), xytext=(x1, 2),
                        arrowprops=dict(arrowstyle="->", color="#333", lw=2))
        ax.set_title("Güvensiz Kanal Üzerinden İletim", fontsize=11, fontweight="bold")
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)

        nav_buttons(next_label="Bob'a geç ▶")

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 6 — Bob decrypts and verifies
    # ══════════════════════════════════════════════════════════════════════════
    elif step == 6:
        d = st.session_state["scen_data"]
        st.subheader("Adım 6 — Bob: Şifre Çözme + İmza Doğrulama")

        tab_dec, tab_ver = st.tabs(["🔓 Şifre Çözme", "🔍 İmza Doğrulama"])

        with tab_dec:
            st.markdown("""
            Bob kendi ortak sırrını (`S_B = d_B × Q_A`) kullanarak şifreyi çözer:
            """)
            n = SECP256K1.n
            dec_rows = [
                {"İşlem": "d_B × Q_A  (Double-and-Add)", "Değer": hex(d["shared_pt_b"][0])[:30] + "..."},
                {"İşlem": "S_B.x (= S_A.x?)",           "Değer": ("✅ Eşit" if d["shared_secret"] == d["shared_pt_b"][0] else "❌ Farklı")},
                {"İşlem": "C XOR S_B.x  (bytes)",       "Değer": d["decrypted"].decode(errors="replace")},
            ]
            st.dataframe(dec_rows, use_container_width=True, hide_index=True)
            st.success(f"Çözülen mesaj: **{d['decrypted'].decode(errors='replace')}**")

        with tab_ver:
            r_v, s_v = d["sig"]
            e_v = hash_message(d["decrypted"])
            w_v = pow(s_v, n - 2, n)
            u1_v = e_v * w_v % n
            u2_v = r_v * w_v % n
            pt_v = SECP256K1.add(
                SECP256K1.scalar_mult(u1_v, SECP256K1.G),
                SECP256K1.scalar_mult(u2_v, d["a_pub"]),
            )
            check = pt_v is not None and pt_v[0] % n == r_v

            ver_rows = [
                {"İşlem": "e = SHA256(mesaj)",      "Değer": hex(e_v)[:28] + "..."},
                {"İşlem": "w = s⁻¹ mod n",          "Değer": hex(w_v)[:28] + "..."},
                {"İşlem": "u₁ = e·w mod n",         "Değer": hex(u1_v)[:28] + "..."},
                {"İşlem": "u₂ = r·w mod n",         "Değer": hex(u2_v)[:28] + "..."},
                {"İşlem": "Nokta = u₁G + u₂·Q_A",  "Değer": f"({hex(pt_v[0])[:14]}..., ...)" if pt_v else "∞"},
                {"İşlem": "Nokta.x mod n",          "Değer": hex(pt_v[0] % n)[:28] + "..." if pt_v else "—"},
                {"İşlem": "== r?",                  "Değer": "✅ EVET — GEÇERLİ" if check else "❌ HAYIR — GEÇERSİZ"},
            ]
            st.dataframe(ver_rows, use_container_width=True, hide_index=True)

            if d["sig_ok"]:
                st.success("✅ İmza GEÇERLİ — Mesaj Alice'ten geldi ve değiştirilmedi!")
            else:
                st.error("❌ İmza GEÇERSİZ!")

        st.divider()
        st.markdown("#### Simülasyon Özeti")
        summary_cols = st.columns(4)
        summary_cols[0].metric("Alice Özel Anahtar", f"{d['a_priv'].bit_length()} bit", "d_A gizli kalır")
        summary_cols[1].metric("Ortak Sır", "256 bit", "S kimseyle paylaşılmaz")
        summary_cols[2].metric("Şifreli Paket", f"{len(d['encrypted'])} byte", "XOR + ECDSA")
        summary_cols[3].metric("Doğrulama", "✅ Başarılı" if d["sig_ok"] else "❌ Başarısız", "ECDSA verify")

        # Final flow diagram
        fig, ax = plt.subplots(figsize=(14, 4.5))
        ax.axis("off"); ax.set_xlim(0, 14); ax.set_ylim(0, 5)
        final_steps = [
            (1.2, 2.5, "Alice\nd_A, Q_A\n(Anahtar Üretimi)",        "#ffcccc"),
            (3.8, 2.5, "ECDH\nS = d_A×Q_B\n= d_B×Q_A",             "#fff3cc"),
            (6.4, 2.5, "Şifrele\nC = M ⊕ S\n(XOR)",                "#cce5ff"),
            (9.0, 2.5, "İmzala\nσ = ECDSA\n(d_A, M)",              "#dff0d8"),
            (11.8, 2.5, "Bob\nÇöz + Doğrula\n✅",                   "#e8d5ff"),
        ]
        for x, y, txt, fc in final_steps:
            r = mpatches.FancyBboxPatch((x - 1.1, y - 1.1), 2.2, 2.2,
                boxstyle="round,pad=0.1", facecolor=fc, edgecolor="gray", lw=1.5)
            ax.add_patch(r)
            ax.text(x, y, txt, ha="center", va="center", fontsize=8.5)
        for i in range(len(final_steps) - 1):
            x1 = final_steps[i][0] + 1.1; x2 = final_steps[i + 1][0] - 1.1
            ax.annotate("", xy=(x2, 2.5), xytext=(x1, 2.5),
                        arrowprops=dict(arrowstyle="->", color="#333", lw=2))
        ax.set_title("ECC ile Güvenli Mesajlaşma — Tam Simülasyon Akışı",
                     fontsize=13, fontweight="bold")
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)

        c1, _, c3 = st.columns([1, 4, 1])
        with c1:
            if st.button("◀ Geri"):
                st.session_state["scen_step"] -= 1
                st.rerun()
        with c3:
            if st.button("🔄 Yeniden Başlat"):
                st.session_state["scen_step"] = 0
                if "scen_data" in st.session_state:
                    del st.session_state["scen_data"]
                st.rerun()



# ══════════════════════════════════════════════════════════════════════════════
# PAGE: Canlı Sohbet
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[12]:
    st.title("💬 Canlı Sohbet — Alice ↔ Bob")
    st.caption("İki taraf iki ayrı sekmede bu sayfayı açar, birbirlerine şifreli mesaj gönderir.")

    # ── helpers ────────────────────────────────────────────────────────────────
    def _connect(role):
        """Register this tab as `role`, generate key pair, publish public key."""
        priv, pub = generate_keypair()
        st.session_state["chat_role"]  = role
        st.session_state["chat_priv"]  = priv
        st.session_state["chat_pub"]   = pub
        state = _chat_load()
        state[role] = _pub_to_dict(pub)
        _chat_save(state)

    def _other(role):
        return "bob" if role == "alice" else "alice"

    def _role_label(role):
        if role == "alice":    return "👩 Alice"
        elif role == "bob":    return "👨 Bob"
        else:                  return "🦹 Saldırıcı"

    def _shared_secret(priv, other_pub_dict):
        other_pub = _dict_to_pub(other_pub_dict)
        pt = SECP256K1.scalar_mult(priv, other_pub)
        return pt[0]   # x-coordinate as shared secret

    def _send(role, priv, shared, text):
        msg_bytes = text.encode()
        encrypted = xor_encrypt(msg_bytes, shared)
        sig       = ecdsa_sign(msg_bytes, priv)
        state     = _chat_load()
        state["messages"].append({
            "from":      role,
            "plain":     text,
            "enc_hex":   encrypted.hex(),
            "sig_r":     hex(sig[0]),
            "sig_s":     hex(sig[1]),
            "ts":        datetime.now().strftime("%H:%M:%S"),
        })
        _chat_save(state)

    def _verify_and_decrypt(msg_rec, shared, sender_pub_dict):
        enc   = bytes.fromhex(msg_rec["enc_hex"])
        plain = xor_encrypt(enc, shared).decode(errors="replace")
        if sender_pub_dict is None:
            return plain, False
        sig = (int(msg_rec["sig_r"], 16), int(msg_rec["sig_s"], 16))
        ok  = ecdsa_verify(plain.encode(), sig, _dict_to_pub(sender_pub_dict))
        return plain, ok

    # ── role selection ─────────────────────────────────────────────────────────
    if "chat_role" not in st.session_state:
        st.markdown("### Bu sekme kim?")
        st.markdown("Alice ve Bob güvenli iletişim kurar. Saldırıcı ise kanalı dinleyip saldırı dener.")
        col_a, col_b, col_e = st.columns(3)
        with col_a:
            if st.button("👩 Alice olarak bağlan", type="primary", use_container_width=True):
                _connect("alice"); st.rerun()
        with col_b:
            if st.button("👨 Bob olarak bağlan", type="primary", use_container_width=True):
                _connect("bob"); st.rerun()
        with col_e:
            if st.button("🦹 Saldırıcı ol", use_container_width=True):
                _connect("attacker"); st.rerun()
        st.stop()

    # ── already connected ──────────────────────────────────────────────────────
    role  = st.session_state["chat_role"]
    priv  = st.session_state["chat_priv"]
    pub   = st.session_state["chat_pub"]

    state = _chat_load()

    if state.get(role) is None:
        state[role] = _pub_to_dict(pub)
        _chat_save(state)

    # ── status bar ─────────────────────────────────────────────────────────────
    alice_ok    = state.get("alice")    is not None
    bob_ok      = state.get("bob")      is not None
    attacker_ok = state.get("attacker") is not None

    sc1, sc2, sc3, sc4, sc5 = st.columns([2, 2, 2, 2, 1])
    with sc1:
        if alice_ok:
            st.success("👩 Alice — bağlı")
        else:
            st.warning("👩 Alice — bekleniyor")
    with sc2:
        if bob_ok:
            st.success("👨 Bob — bağlı")
        else:
            st.warning("👨 Bob — bekleniyor")
    with sc3:
        if attacker_ok:
            st.error("🦹 Eve — kanalda!")
        else:
            st.info("🦹 Eve — yok")
    with sc4:
        st.info(f"Mesaj sayısı: {len(state['messages'])}")
    with sc5:
        if st.button("🔄 Yenile"): st.rerun()

    st.divider()

    # ══════════════════════════════════════════════════════════════════════════
    # ATTACKER VIEW
    # ══════════════════════════════════════════════════════════════════════════
    if role == "attacker":
        st.subheader("🦹 Saldırıcı — Saldırgan Paneli")

        tab_spy, tab_forge, tab_brute = st.tabs(["👁️ Kanal Dinleme", "✉️ Mesaj Sahteciliği", "💥 Kaba Kuvvet"])

        with tab_spy:
            st.markdown("#### Kanaldan topladığın bilgiler")
            spy1, spy2 = st.columns(2)
            with spy1:
                st.markdown("**Açık Anahtarlar (herkese görünür)**")
                if alice_ok:
                    apd = state["alice"]
                    st.code(f"Q_A.x = {apd['x'][:24]}...\nQ_A.y = {apd['y'][:24]}...", language="text")
                else:
                    st.warning("Alice henüz bağlanmadı.")
                if bob_ok:
                    bpd = state["bob"]
                    st.code(f"Q_B.x = {bpd['x'][:24]}...\nQ_B.y = {bpd['y'][:24]}...", language="text")
                else:
                    st.warning("Bob henüz bağlanmadı.")
            with spy2:
                st.markdown("**Bildiklerin vs. bilmediklerin**")
                st.success("✅ Q_A, Q_B — açık anahtarlar")
                st.success("✅ G — sabit generator")
                st.success("✅ Şifreli mesajlar (hex)")
                st.error("❌ d_A, d_B — ECDLP çözülemez")
                st.error("❌ S = d_A × d_B × G — ortak sır")

            st.divider()
            st.markdown("#### Şifreli mesajları okuma denemesi")
            msgs = state.get("messages", [])
            if not msgs:
                st.info("Kanalda henüz mesaj yok.")
            else:
                for m in msgs:
                    if m.get("forged"):
                        st.markdown(f"**[KENDİ SAHTECİLİĞİN]** `{m['ts']}` → `{m['enc_hex'][:48]}...`")
                        continue
                    sender = "👩 Alice" if m["from"] == "alice" else "👨 Bob"
                    st.markdown(f"**{sender}** `{m['ts']}` → `{m['enc_hex'][:48]}...`")
                    with st.expander(f"🔓 Çözme denemesi — {m['ts']}"):
                        fake_secret = int(hashlib.sha256(b"eve_fake").hexdigest(), 16)
                        garbled = xor_encrypt(bytes.fromhex(m["enc_hex"]), fake_secret).decode(errors="replace")
                        st.error(f"Yanlış anahtarla çözülen: `{garbled}`")
                        st.caption("Ortak sır S bilinmeden doğru çözüm imkânsız.")

        with tab_forge:
            st.markdown("#### Alice'miş gibi sahte mesaj gönder")
            st.warning("Mesaj Alice'in **d_A** özel anahtarı olmadan imzalanacak → Bob'da ❌ görünecek.")
            if not (alice_ok and bob_ok):
                st.info("Alice ve Bob'un ikisi de bağlı olmalı.")
            else:
                forge_msg = st.text_input("Sahte mesaj:", value="Bob, tüm parayı Saldırıcı'e gönder!")
                if st.button("🚀 Sahte Mesaj Gönder (Alice gibi)", type="primary"):
                    msg_b      = forge_msg.encode()
                    sig_e      = ecdsa_sign(msg_b, priv)          # signed with Saldırıcı's key, NOT Alice's
                    fake_key   = random.randint(1, SECP256K1.n - 1)
                    enc_fake   = xor_encrypt(msg_b, fake_key)     # encrypted with wrong key
                    s = _chat_load()
                    s["messages"].append({
                        "from":    "alice",
                        "plain":   forge_msg,
                        "enc_hex": enc_fake.hex(),
                        "sig_r":   hex(sig_e[0]),
                        "sig_s":   hex(sig_e[1]),
                        "ts":      datetime.now().strftime("%H:%M:%S"),
                        "forged":  True,
                    })
                    _chat_save(s)
                    st.success("Gönderildi! Bob sekmesini yenile — ❌ SAHTE olarak görünecek.")
                    st.rerun()

                st.divider()
                st.markdown("""
                **Neden başarısız?**
                - Bob imzayı **Q_A** ile doğrular → sig **d_E** ile yapıldı → ❌
                - Şifre **yanlış key** ile yapıldı → çözünce anlamsız metin
                """)

        with tab_brute:
            st.markdown("#### Özel Anahtarı Kaba Kuvvetle Bulmaya Çalış")
            st.error("Gerçek secp256k1'de tamamen imkânsız — bu sadece küçük sayılarla demo.")
            if alice_ok:
                apd    = state["alice"]
                a_pt   = _dict_to_pub(apd)
                tries  = st.slider("Kaç k dene?", 10, 1000, 200)
                if st.button("💥 Brute Force Başlat"):
                    found = None
                    for k in range(1, tries + 1):
                        if SECP256K1.scalar_mult(k, SECP256K1.G) == a_pt:
                            found = k; break
                    if found:
                        st.success(f"Bulundu: d_A = {found}  (gerçek d_A 256-bit — bu sadece şansa bağlı!)")
                    else:
                        st.error(f"{tries} denemede bulunamadı.")
                        st.caption(f"Gerçek uzayda ~10⁷⁷ olasılık var. 10⁹/sn hızla: ~10⁶⁸ yıl.")
            else:
                st.info("Alice bağlı değil.")

        st.divider()
        if st.button("🚪 Saldırıyı Bitir / Bağlantıyı Kes"):
            s = _chat_load(); s["attacker"] = None; _chat_save(s)
            del st.session_state["chat_role"]
            del st.session_state["chat_priv"]
            del st.session_state["chat_pub"]
            st.rerun()

    # ══════════════════════════════════════════════════════════════════════════
    # ALICE / BOB VIEW
    # ══════════════════════════════════════════════════════════════════════════
    else:
        other          = _other(role)
        other_pub_dict = state.get(other)
        connected      = other_pub_dict is not None

        with st.expander("🔑 Anahtar bilgileri"):
            k1, k2 = st.columns(2)
            with k1:
                st.markdown(f"**{_role_label(role)} — Benim anahtarlarım**")
                st.code(
                    f"Özel (d): {hex(priv)[:20]}...\n"
                    f"Açık  (x): {hex(pub[0])[:20]}...\n"
                    f"Açık  (y): {hex(pub[1])[:20]}...",
                    language="text"
                )
            with k2:
                if connected:
                    other_pub = _dict_to_pub(other_pub_dict)
                    shared    = _shared_secret(priv, other_pub_dict)
                    st.markdown(f"**{_role_label(other)} — Karşı tarafın açık anahtarı**")
                    st.code(
                        f"Açık  (x): {hex(other_pub[0])[:20]}...\n"
                        f"Açık  (y): {hex(other_pub[1])[:20]}...\n\n"
                        f"ECDH Ortak Sır:\n{hex(shared)[:30]}...",
                        language="text"
                    )
                else:
                    st.info("Diğer taraf bağlandığında ortak sır hesaplanacak.")

        if not connected:
            st.info(f"Diğer sekmede **{_role_label(other)}** olarak bağlanılmasını bekliyor… "
                    "Bağlandıktan sonra 🔄 Yenile butonuna bas.")
        else:
            shared = _shared_secret(priv, other_pub_dict)
            msgs   = state.get("messages", [])

            if not msgs:
                st.markdown("_Henüz mesaj yok. İlk mesajı gönder!_")
            else:
                for m in msgs:
                    sender_is_me = m["from"] == role
                    is_forged    = m.get("forged", False)
                    align_style  = "margin-left:auto" if sender_is_me else "margin-right:auto"

                    if is_forged:
                        bg_color     = "#3d0000"
                        sender_label = "👩 Alice ⚠️ [SAHTECİLİK ŞÜPHESİ]"
                    else:
                        bg_color     = "#d4f0d4" if sender_is_me else "#d4e4f0"
                        sender_label = _role_label(m["from"])

                    sender_pub_dict = state.get(m["from"])
                    plain, sig_ok   = _verify_and_decrypt(m, shared, sender_pub_dict)

                    if is_forged:
                        sig_badge  = "❌ İMZA GEÇERSİZ — SAHTE MESAJ TESPİT EDİLDİ"
                        sig_color  = "#ff4444"
                        plain_show = "[ŞİFRE ÇÖZÜLEMEZ — yanlış anahtar]"
                    else:
                        sig_badge  = "✅ İmza geçerli" if sig_ok else "❌ İmza geçersiz"
                        sig_color  = "#2ecc71" if sig_ok else "#e74c3c"
                        plain_show = plain

                    st.markdown(f"""
<div style="max-width:70%;{align_style};background:{bg_color};border-radius:12px;
     padding:10px 14px;margin:6px 0;">
  <div style="font-size:12px;color:#aaa;margin-bottom:4px;">
    {sender_label} &nbsp;·&nbsp; {m['ts']}
  </div>
  <div style="font-size:16px;margin-bottom:6px;"><b>{plain_show}</b></div>
  <span style="font-size:11px;color:{sig_color}">{sig_badge}</span>
</div>""", unsafe_allow_html=True)

                    with st.expander(f"🔬 Detaylar — {m['ts']}", expanded=False):
                        d1, d2 = st.columns(2)
                        with d1:
                            st.markdown("**Şifreli (hex)**")
                            st.code(m["enc_hex"], language="text")
                        with d2:
                            st.markdown("**ECDSA İmza (r, s)**")
                            st.code(f"r = {m['sig_r'][:24]}...\ns = {m['sig_s'][:24]}...", language="text")

            st.divider()
            with st.form("send_form", clear_on_submit=True):
                inp_col, btn_col = st.columns([5, 1])
                with inp_col:
                    msg_input = st.text_input(
                        "Mesajını yaz:",
                        placeholder=f"{_role_label(role)} olarak mesaj gönder…",
                        label_visibility="collapsed"
                    )
                with btn_col:
                    send = st.form_submit_button("Gönder 📤", use_container_width=True)

            if send and msg_input.strip():
                _send(role, priv, shared, msg_input.strip())
                st.rerun()

        st.divider()
        c1, c2 = st.columns(2)
        with c1:
            if st.button("🔄 Sohbeti Sıfırla"):
                s = _chat_load(); s["messages"] = []; _chat_save(s); st.rerun()
        with c2:
            if st.button("🚪 Rolü Değiştir / Bağlantıyı Kes"):
                s = _chat_load(); s[role] = None; _chat_save(s)
                del st.session_state["chat_role"]
                del st.session_state["chat_priv"]
                del st.session_state["chat_pub"]
                st.rerun()
