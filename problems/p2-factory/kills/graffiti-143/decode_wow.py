#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Decode the Type-3 glyph-name text extracted from wow-july2004.pdf.
Glyph names are /XY with X,Y base-36 digits: char = chr(36*v(X) + v(Y) - 360).
(Verified against the document title "Written on the Wall" and body text.)

Usage:
  python decode_wow.py            # extracts text from wow-july2004.pdf (pypdf)
                                  # and writes wow_decoded_test.txt
"""
import re

A36 = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"


def decode(raw):
    def dec(m):
        s = m.group(0)[1:]
        v = A36.index(s[0]) * 36 + A36.index(s[1]) - 360
        return chr(v) if 0 <= v < 0x110000 else '?'
    return re.sub(r'/[0-9A-Z][0-9A-Z]', dec, raw)


def main():
    from pypdf import PdfReader
    r = PdfReader('wow-july2004.pdf')
    raw = '\n@@PAGE@@\n'.join((p.extract_text() or '') for p in r.pages)
    with open('wow_extracted_raw.txt', 'w', encoding='utf-8') as fh:
        fh.write(raw)
    txt = decode(raw)
    with open('wow_decoded_test.txt', 'w', encoding='utf-8') as fh:
        fh.write(txt)
    # show the conjecture-143 block as a sanity check
    norm = re.sub(r'\s+', ' ', txt)
    k = norm.find('143. varianc')
    print(norm[k - 300:k + 300])


if __name__ == '__main__':
    main()
