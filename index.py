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
# PAGE: Canlı Sohbet
# ══════════════════════════════════════════════════════════════════════════════
elif page == PAGES[4]:
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
