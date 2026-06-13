import os
import pypdf
d = os.path.dirname(os.path.abspath(__file__))
r = pypdf.PdfReader(os.path.join(d, "paper.pdf"))
out = []
for i, pg in enumerate(r.pages):
    out.append(f"\n===== PAGE {i+1} =====\n")
    out.append(pg.extract_text() or "")
open(os.path.join(d, "paper_pdf.txt"), "w", encoding="utf-8").write("\n".join(out))
print("pages:", len(r.pages))
