"""Generate local-only contact sheets for exhaustive PDF layout review."""
import json
from pathlib import Path
from PIL import Image, ImageDraw

ROOT=Path(__file__).resolve().parent
trace=json.loads((ROOT/'inputs/trace-index.json').read_text(encoding='utf-8'))
out=ROOT/'qa'
out.mkdir(exist_ok=True)
for paper in trace['papers']:
    for start in range(0,len(paper['pages']),12):
        sheet=Image.new('RGB',(1120,1190),'#e8edf4')
        draw=ImageDraw.Draw(sheet)
        for i,page in enumerate(paper['pages'][start:start+12]):
            with Image.open(ROOT/'inputs'/page['file']) as im:
                im=im.convert('RGB');im.thumbnail((260,358))
                x=10+(i%4)*280;y=24+(i//4)*395
                draw.text((x,y-18),paper['id']+' page '+str(page['page']),fill='#102030')
                sheet.paste(im,(x,y))
        sheet.save(out/(paper['id']+'-layout-'+str(start//12+1)+'.jpg'),quality=90)
print('Generated contact sheets for all',sum(len(p['pages']) for p in trace['papers']),'PDF pages.')
