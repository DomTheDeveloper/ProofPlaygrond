"""Recheck the extension at every prime, including all exponent vectors."""
from pathlib import Path
import json
from math import isqrt
from search_fixed_points import examine
from check_fixed_points import verify
root=Path(__file__).resolve().parent
data=json.loads((root/'counts.json').read_text())
bound=data['least_prime_limit']
old=0
new=0
for p in range(2,bound+1):
    if any(p%d==0 for d in range(2,isqrt(p)+1)):
        continue
    count=data['by_prime'][str(p)]
    if p<=199:
        old+=count
        continue
    i,nodes,ih=examine(p)
    r,rh=verify(p)
    assert i==r==count and ih==rh==[], (p,i,r,ih,rh)
    print(p,count,ih,flush=True)
    new+=count
assert old==89439 and new==data['additional_patterns'] and old+new==data['total_patterns']
print(f"{old+new:,} exponent patterns through {bound}; sole fixed point 21.")
