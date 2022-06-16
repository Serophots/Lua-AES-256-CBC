const CryptoJS = require('crypto-js'); //npm install crypto-js

const hex = {
    fromString: str => {
        let arr = [];
        for (let i = 0, l = str.length; i < l; i ++) {
            let hex = Number(str.charCodeAt(i)).toString(16);
          arr.push(hex);
        }
        return arr.join('');
    },
    toString: hexx => {
        let hex = hexx.toString();//force conversion
        let str = '';
        for (let i = 0; i < hex.length; i += 2)
            str += String.fromCharCode(parseInt(hex.substr(i, 2), 16));
        return str;
    }
}
const crypt = {
    encrypt: (plaintext, key, iv) => CryptoJS.AES.encrypt(CryptoJS.enc.Hex.parse(plaintext), CryptoJS.enc.Hex.parse(key), { mode: CryptoJS.mode.CBC, padding: CryptoJS.pad.NoPadding, iv: CryptoJS.enc.Hex.parse(iv)}).ciphertext.toString(),
    decrypt: (ciphertext, key, iv) => CryptoJS.AES.decrypt({ciphertext: CryptoJS.enc.Hex.parse(ciphertext)}, CryptoJS.enc.Hex.parse(key), { mode: CryptoJS.mode.CBC, padding: CryptoJS.pad.NoPadding, iv: CryptoJS.enc.Hex.parse(iv)}).toString(),

    
    decode: (encoded) => {
        return hex.toString(encoded).replaceAll("#", "")
    },
    encode: (plain) => {
        while (plain.length*2%32 != 0) plain=plain+"#"
        return hex.fromString(plain)
    },
}
//crypt.decrypt/encrypt is raw AES encryption where input text size matters + must be hex
//crypt.decode/encode is my own padding which allows you to enter any plaintext
//Other values, ei key + iv must be hex strings of correct sizes

const e = crypt.encrypt(crypt.encode("lemon pickles"), "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4", "000102030405060708090A0B0C0D0E0F")
console.log("Encrypted", e)
console.log("Decrypted", crypt.decode(crypt.decrypt(e, "f643003eb676e550e3c00fdc1ece26f9cc3562885ead4c8f88aa87c58b73088c", "0b1515f29119e00fba5853e95d33943e").toString()))
