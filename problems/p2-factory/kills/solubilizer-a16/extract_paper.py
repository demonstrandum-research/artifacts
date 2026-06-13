import re, html, os
d = os.path.dirname(os.path.abspath(__file__))
s = open(os.path.join(d, "paper.html"), encoding="utf-8").read()
# Replace math elements with their LaTeX alttext
s = re.sub(r'<math[^>]*alttext="(.*?)"[^>]*>.*?</math>',
           lambda m: " " + html.unescape(m.group(1)) + " ", s, flags=re.S)
s = re.sub(r'<(script|style).*?</\1>', ' ', s, flags=re.S)
s = re.sub(r'<[^>]+>', ' ', s)
s = html.unescape(s)
s = re.sub(r'[ \t]+', ' ', s)
open(os.path.join(d, "paper.txt"), "w", encoding="utf-8").write(s)
print("wrote", len(s), "chars")
