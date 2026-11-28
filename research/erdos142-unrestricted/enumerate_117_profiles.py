"""Conditional numerical profile list; external exclusions are assumptions."""
import itertools,collections,json
upper=[16,17,17,16,16]
profiles=[]
for c in itertools.product(*(range(7,u+1) for u in upper)):
    if sum(c)!=69 or c[1]==c[2]==17:continue
    reflected=(c[3],c[2],c[1],c[0],c[4])
    if c<=reflected:profiles.append(c)
print(json.dumps({'residue_order':[0,1,2,3,4],'profiles_up_to_reflection':len(profiles),
 'labelled_profiles':sum(1 if c==(c[3],c[2],c[1],c[0],c[4]) else 2 for c in profiles),
 'by_minimum_size':dict(sorted(collections.Counter(min(c) for c in profiles).items())),
 'profiles':profiles},indent=2))
