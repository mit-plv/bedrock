#!/usr/bin/python
import sys
import shutil
import re
import os.path

def uncomment(tkn, data):
    return re.sub(r"\(\*%s(([^*]|(\*[^)]))+)\*\)" % tkn, r"\1", data)

def process_file(src, trg):
    data = open('%s.v' % src,'r').read()
    if '(*TIME' in data:
        f = open('%s.v' % trg, 'w')
        f.write(uncomment("TIME", data))
        f.close()
    else:
        for ext in ['v','v.d','vo','glob']:
            try:
                shutil.copyfile('%s.%s' % (src,ext), '%s.%s' % (trg,ext))
            except:
                pass

def main(temp_dir, files):
    for f in files:
        assert f.endswith('.v')
        process_file(f[:-2], os.path.join(temp_dir, f[:-2]))

# timer.py [temp_dir] [files+]
if __name__ == '__main__':
    assert len(sys.argv) > 2

    main(sys.argv[1], sys.argv[2:])
