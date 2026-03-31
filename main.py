import ecdsa
import hashlib

# 1. ADIM: Anahtar Çifti Oluşturma
# NIST256p veya SECP256k1 (Bitcoin eğrisi) tercih edilebilir
sk = ecdsa.SigningKey.generate(curve=ecdsa.SECP256k1) 
vk = sk.verifying_key # Açık Anahtar (Public Key)

print(f"--- Anahtarlar Oluşturuldu ---")
print(f"Özel Anahtar (Hex): {sk.to_string().hex()}")
print(f"Açık Anahtar (Hex): {vk.to_string().hex()}\n")

# 2. ADIM: Mesajı İmzalama
mesaj = b"Bu mesaj ECC ile guvence altina alinmistir."
imza = sk.sign(mesaj)

print(f"--- İmzalama İşlemi ---")
print(f"Mesaj: {mesaj.decode()}")
print(f"Oluşan Dijital İmza (Hex): {imza.hex()}\n")

# 3. ADIM: Doğrulama (Verification)
print(f"--- Doğrulama Sonucu ---")
try:
    if vk.verify(imza, mesaj):
        print("✅ Başarılı: İmza geçerli, veri değiştirilmemiş!")
except ecdsa.BadSignatureError:
    print("❌ Hata: Geçersiz imza veya değiştirilmiş veri!")

# Bonus: Veri değiştirilirse ne olur?
sahte_mesaj = b"Bu mesaj degistirildi."
try:
    vk.verify(imza, sahte_mesaj)
except ecdsa.BadSignatureError:
    print(f"\n⚠️ Güvenlik Testi: Mesaj '{sahte_mesaj.decode()}' olarak değiştirildiği için imza reddedildi.")