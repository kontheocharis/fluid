stack run -- -c ./start.fluid

stack run -- -r ./start.fluid -n add-index -a 'data=Expr, type=`List V`, index=0' > step1.fluid
stack run -- -c ./step1.fluid

stack run -- -r ./step1.fluid -n unify-inds -a 'data=Expr, ctor=Add, indsToUnify=[5,3,1]' > step2a.fluid
stack run -- -c ./step2a.fluid

stack run -- -r ./step2a.fluid -n rel-ctor-params -a 'data=Expr, ctor=Var, inds=[2,1], reln=`Elem`' > step2b.fluid
stack run -- -c ./step2b.fluid

stack run -- -r ./step2b.fluid -n add-param -a 'func=lookupVar, index=0, type=`List V`' > step3a.fluid
stack run -- -c ./step3a.fluid

# Broken: RelFuncParams duplicates holes in recursive call
# stack run -- -r ./step3a.fluid -n rel-func-params -a 'func=lookupVar, inds=[2,3], reln=`Elem`' > step3b.fluid
stack run -- -c ./step3b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
# stack run -- -c ./step3c.fluid

stack run -- -r ./step3b.fluid -n expand-pattern -a 'func=lookupVar, index=0' > step3b1.fluid
stack run -- -r ./step3b1.fluid -n expand-pattern -a 'func=lookupVar, index=2' > step3c1.fluid


# stack run -- -r ./step3b.fluid -n expand-pattern -a "pos=31:18" > step3c1.fluid
# stack run -- -r ./step3c1.fluid -n expand-pattern -a "pos=31:11" > step3c2.fluid

stack run -- -r ./step3c1.fluid -n identify-impossibles -a 'decl=lookupVar' > step3c.fluid

# stack run -- -r ./step3c3.fluid -n expand-pattern -a "pos=33:11" > step3c.fluid

# stack run -- -r ./step3c1.fluid -n expand-pattern -a "pos=31:11" > step3c1.fluid 

stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

# Manual: fill holes
stack run -- -c ./step4.fluid

stack run -- -r ./step4.fluid -n add-param -a 'func=eval, index=0, type=`List Nat`' > step5a.fluid
stack run -- -c ./step5a.fluid

# Broken: does not add recursive holes
# stack run -- -r ./step5a.fluid -n rel-func-params -a 'func=eval, inds=[3,2,4], reln=`Unzip`' > step5b.fluid
stack run -- -c ./step5b.fluid

echo 'step5c'
stack run -- -r ./step5b.fluid -n expand-pattern -a "func=eval, index=0" > step5c1.fluid

echo 'step5c1'
stack run -- -r ./step5c1.fluid -n expand-pattern -a "func=eval, index=1" > step5c2.fluid

echo 'step5c2'
stack run -- -r ./step5c2.fluid -n identify-impossibles -a 'decl=eval' > step5c3.fluid

echo 'step5c3'
stack run -- -r ./step5c3.fluid -n identify-impossibles -a 'decl=eval' > step5c4.fluid
stack run -- -r ./step5c4.fluid -n expand-pattern -a "func=eval, index=2" > step5c5.fluid
stack run -- -r ./step5c5.fluid -n identify-impossibles -a 'decl=eval' > step5c6.fluid

echo 'step5c6'
stack run -- -r ./step5c6.fluid -n expand-pattern -a "func=eval, index=3" > step5c7.fluid
stack run -- -r ./step5c7.fluid -n identify-impossibles -a 'decl=eval' > step5c8.fluid

echo 'step5c8'
stack run -- -r ./step5c8.fluid -n expand-pattern -a "func=eval, index=4" > step5c.fluid

#stack run -- -r ./step5b1.fluid -n expand-pattern -a "pos=42:6" > step5b2.fluid
#stack run -- -r ./step5b2.fluid -n expand-pattern -a "pos=40:15" > step5b3.fluid

# stack run -- -r ./step5b3.fluid -n identify-impossibles -a 'decl=eval' > step5b4.fluid

# stack run -- -r ./step5b4.fluid -n expand-pattern -a "pos=42:9" > step5b5.fluid

# stack run -- -r ./step5b4.fluid -n expand-pattern -a "pos=40:26" > step5b5.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
stack run -- -c ./step5c.fluid

# Temporary to check bool tautology removal:
stack run -- -r ./boolean-tautology.fluid -n rm-taut -a 'lx=35, ly=64, op=isEqual' > boolean-tautology2.fluid
stack run -- -c ./boolean-tautology2.fluid
