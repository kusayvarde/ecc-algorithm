import streamlit as st
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import hashlib
import random

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

    st.markdown("""
    Bu uygulama ECC'nin çalışma prensibini **adım adım** göstermektedir.
    Tüm matematiksel işlemler **sıfırdan Python ile** yazılmıştır.

    ---

    ### Bu uygulamada neler var?

    | # | Bölüm | Açıklama |
    |---|-------|----------|
    | 1 | 📐 Eliptik Eğriler | y² = x³ + ax + b eğri ailesi |
    | 2 | ➕ Nokta Toplama | Geometrik anlam, P+Q ve 2P |
    | 3 | ✖️ Skaler Çarpım | k×P — interaktif animasyon |
    | 4 | 🔢 Sonlu Alan | mod p üzerinde nokta dağılımı |
    | 5 | ⚡ Double-and-Add | Verimli hesaplama algoritması |
    | 6 | 🔑 Anahtar Üretimi | Tek yönlü fonksiyon |
    | 7 | 🤝 ECDH | Güvenli anahtar değişimi |
    | 8 | ✍️ ECDSA | Dijital imza oluşturma ve doğrulama |
    | 9 | 🛡️ Güvenlik Testi | Manipülasyon denemeleri |
    | 10 | 📊 ECC vs RSA | Karşılaştırmalı analiz |
    | 11 | 📨 Tam Senaryo | Alice → Bob güvenli mesaj |
    """)

    st.divider()
    col1, col2, col3 = st.columns(3)
    col1.metric("secp256k1 p boyutu", "256 bit", "~10⁷⁷ olasılık")
    col2.metric("RSA denk güvenlik", "3072 bit", "12× daha büyük")
    col3.metric("Double-and-Add adımı", "O(log k)", "Naif: O(k)")

    st.info("Sol menüden bir bölüm seçerek başlayın.")


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
    P0 = (-1.0, np.sqrt(6))

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
        draw_real_curve(ax, 0, 7, xlim=(-3, 5), ylim=(-8, 8))
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

    st.info("Noktalar eğri üzerinde tahmin edilemez bir şekilde 'atlıyor' — bu rastgelelik güvenliği sağlar!")


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

    # Akış diyagramı
    with st.expander("📊 ECDSA Akış Diyagramı"):
        fig, axes = plt.subplots(1, 2, figsize=(12, 7))

        def fbox(ax, x, y, txt, col="#f0f0ff", w=2.2, h=0.6):
            r = mpatches.FancyBboxPatch((x - w / 2, y - h / 2), w, h,
                boxstyle="round,pad=0.08", facecolor=col, edgecolor="#555", lw=1.2)
            ax.add_patch(r)
            ax.text(x, y, txt, ha="center", va="center", fontsize=8.5)

        sign_steps = [
            (2, 8.5, "mesaj (bytes)",        "#ffe0cc"),
            (2, 7.3, "e = SHA256(mesaj)",    "#fff3cc"),
            (2, 6.1, "k = rand(1, n−1)",     "#e8f4fd"),
            (2, 4.9, "R = k × G",            "#e8f4fd"),
            (2, 3.7, "r = R.x  mod n",       "#e8f4fd"),
            (2, 2.5, "s = k⁻¹(e+r·d) mod n","#dff0d8"),
            (2, 1.3, "İmza = (r, s)",        "#d4edda"),
        ]
        ax = axes[0]; ax.set_xlim(0, 4); ax.set_ylim(0, 10); ax.axis("off")
        ax.set_title("İmzalama", fontsize=11, fontweight="bold")
        for x, y, t, c in sign_steps:
            fbox(ax, x, y, t, c)
        for i in range(len(sign_steps) - 1):
            _, y1, _, _ = sign_steps[i]; _, y2, _, _ = sign_steps[i + 1]
            ax.annotate("", xy=(2, y2 + 0.3), xytext=(2, y1 - 0.3),
                        arrowprops=dict(arrowstyle="->", color="#333", lw=1.5))
        ax.text(0.2, 2.2, "d = özel\nanahtar", fontsize=7.5, color="red", style="italic")

        verify_steps = [
            (2, 8.5, "mesaj + imza (r,s)",      "#ffe0cc"),
            (2, 7.3, "e = SHA256(mesaj)",        "#fff3cc"),
            (2, 6.1, "w = s⁻¹  mod n",          "#e8f4fd"),
            (2, 4.9, "u₁=e·w, u₂=r·w  mod n",  "#e8f4fd"),
            (2, 3.7, "Nokta = u₁G + u₂Q",       "#e8f4fd"),
            (2, 2.5, "Nokta.x  mod n == r?",    "#fff3cc"),
            (2, 1.3, "GEÇERLİ / GEÇERSİZ",     "#d4edda"),
        ]
        ax = axes[1]; ax.set_xlim(0, 4); ax.set_ylim(0, 10); ax.axis("off")
        ax.set_title("Doğrulama", fontsize=11, fontweight="bold")
        for x, y, t, c in verify_steps:
            fbox(ax, x, y, t, c)
        for i in range(len(verify_steps) - 1):
            _, y1, _, _ = verify_steps[i]; _, y2, _, _ = verify_steps[i + 1]
            ax.annotate("", xy=(2, y2 + 0.3), xytext=(2, y1 - 0.3),
                        arrowprops=dict(arrowstyle="->", color="#333", lw=1.5))
        ax.text(0.1, 3.4, "Q = açık\nanahtar", fontsize=7.5, color="blue", style="italic")

        fig.suptitle("ECDSA Akış Diyagramı", fontsize=12, fontweight="bold")
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)


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
    st.caption("💡 Tüm adımların gerçek bir kullanım senaryosunda bir arada nasıl çalıştığını görmek için.")
    st.markdown("ECDH + ECDSA birlikte: şifreli **ve** imzalı mesaj gönderimi")

    msg_text = st.text_input("Alice'in mesajı:", "Merhaba Bob! Bu tamamen gizli.")

    if st.button("🚀 Senaryoyu Çalıştır", type="primary"):
        with st.spinner("Hesaplanıyor..."):
            a_priv, a_pub = generate_keypair()
            b_priv, b_pub = generate_keypair()

            # ECDH
            shared_pt_a = SECP256K1.scalar_mult(a_priv, b_pub)
            shared_pt_b = SECP256K1.scalar_mult(b_priv, a_pub)
            shared_secret = shared_pt_a[0]

            # Şifreleme
            msg_bytes = msg_text.encode()
            encrypted = xor_encrypt(msg_bytes, shared_secret)

            # İmzalama
            sig = ecdsa_sign(msg_bytes, a_priv)

            # Bob tarafı
            decrypted = xor_encrypt(encrypted, shared_pt_b[0])
            sig_ok = ecdsa_verify(decrypted, sig, a_pub)

        st.divider()
        col1, col2 = st.columns(2)

        with col1:
            st.subheader("👩 Alice")
            st.markdown("**1. Anahtar üretimi**")
            st.code(f"d_A = {hex(a_priv)[:25]}...", language="text")
            st.markdown("**2. ECDH ortak sır**")
            st.code(f"S = d_A × Q_B\n  = {hex(shared_secret)[:25]}...", language="text")
            st.markdown("**3. Mesajı XOR şifrele**")
            st.code(f"Orijinal : {msg_text}\nŞifreli  : {encrypted.hex()[:30]}...", language="text")
            st.markdown("**4. Mesajı imzala (ECDSA)**")
            st.code(f"r = {hex(sig[0])[:20]}...\ns = {hex(sig[1])[:20]}...", language="text")

        with col2:
            st.subheader("👨 Bob")
            st.markdown("**5. ECDH ortak sır (aynı)**")
            st.code(f"S = d_B × Q_A\n  = {hex(shared_pt_b[0])[:25]}...", language="text")
            st.markdown("**6. Şifreyi çöz**")
            st.code(f"Çözülen: {decrypted.decode()}", language="text")
            st.markdown("**7. İmzayı doğrula**")
            if sig_ok:
                st.success("✅ İmza GEÇERLİ\nMesaj Alice'ten geldi, değiştirilmedi!")
            else:
                st.error("❌ İmza GEÇERSİZ")

        # Akış görseli
        fig, ax = plt.subplots(figsize=(14, 4.5))
        ax.axis("off"); ax.set_xlim(0, 14); ax.set_ylim(0, 5)
        steps = [
            (1,   2.5, "Alice\nAnahtar Çifti\n(d_A, Q_A)",             "#ffcccc"),
            (3.5, 2.5, "ECDH\nOrtak Sır\nS = d_A × Q_B",              "#fff3cc"),
            (6,   2.5, "XOR\nŞifreleme\nC = Enc(M, S)",               "#cce5ff"),
            (8.5, 2.5, "ECDSA\nİmzalama\nσ = Sign(M, d_A)",           "#dff0d8"),
            (11,  2.5, "Bob\nÇöz + Doğrula\nM=Dec(C,S), Verify(M,σ)", "#e8d5ff"),
        ]
        for x, y, txt, col in steps:
            r = mpatches.FancyBboxPatch((x - 1, y - 1), 2, 2,
                boxstyle="round,pad=0.1", facecolor=col, edgecolor="gray", lw=1.5)
            ax.add_patch(r)
            ax.text(x, y, txt, ha="center", va="center", fontsize=8.5)
        for i in range(len(steps) - 1):
            x1 = steps[i][0] + 1; x2 = steps[i + 1][0] - 1
            ax.annotate("", xy=(x2, 2.5), xytext=(x1, 2.5),
                        arrowprops=dict(arrowstyle="->", color="#333", lw=2))
        ax.set_title("ECC ile Güvenli Mesajlaşma — Tam Akış", fontsize=13, fontweight="bold")
        plt.tight_layout()
        st.pyplot(fig)
        plt.close(fig)

    else:
        st.info("Mesajı girin ve 'Senaryoyu Çalıştır' düğmesine basın.")

    st.divider()
    st.markdown("""
    ### Özet

    | Kavram | Açıklama |
    |--------|----------|
    | **Eliptik Eğri** | y² = x³ + ax + b — özel cebirsel yapı |
    | **Nokta Toplama** | Geometrik işlem, deterministic |
    | **Skaler Çarpım** | k × P — hızlı hesaplanır |
    | **ECDLP** | k×P'den k bulmak imkânsız |
    | **Özel Anahtar** | Rastgele d (gizli) |
    | **Açık Anahtar** | Q = d × G (herkese açık) |
    | **ECDH** | Güvensiz kanalda ortak sır |
    | **ECDSA** | Mesaj bütünlüğü + kimlik doğrulama |

    **Gerçek hayat kullanımı:** Bitcoin/Ethereum, TLS 1.3 (HTTPS), SSH, Signal, WhatsApp
    """)
