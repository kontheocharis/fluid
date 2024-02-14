stack run -- -c ./start.fluid

echo "Step 1"
stack run -- -r ./start.fluid -n add-index -a 'data=Expr, type=`List V`, index=0, name=vars' > step1.fluid
stack run -- -c ./step1.fluid

echo "Step 2a"
stack run -- -r ./step1.fluid -n unify-inds -a 'data=Expr, ctor=Add, indsToUnify=[5,3,1]' > step2a.fluid
stack run -- -c ./step2a.fluid

echo "Step 2b"
stack run -- -r ./step2a.fluid -n rel-ctor-params -a 'data=Expr, ctor=Var, inds=[2,1], reln=`Elem`' > step2b.fluid
stack run -- -c ./step2b.fluid

echo "Step 3a"
stack run -- -r ./step2b.fluid -n add-param -a 'func=lookupVar, index=0, type=`List V`, name=patV' > step3a.fluid
stack run -- -c ./step3a.fluid

echo "Step 3b"
stack run -- -r ./step3a.fluid -n rel-func-params -a 'func=lookupVar, inds=[2,3], reln=`Elem`' > step3b.fluid
stack run -- -c ./step3b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
# stack run -- -c ./step3c.fluid
echo "Step 3d"
stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

# Manual: fill holes + pattern expansion
echo "Step 4"
stack run -- -c ./step4.fluid

echo "Step 5a"
stack run -- -r ./step4.fluid -n add-param -a 'func=eval, index=0, type=`List Nat`, name=patV1' > step5a.fluid
stack run -- -c ./step5a.fluid

echo "Step 5b"
stack run -- -r ./step5a.fluid -n rel-func-params -a 'func=eval, inds=[3,2,4], reln=`Unzip`' > step5b.fluid
stack run -- -c ./step5b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
# stack run -- -c ./step5c.fluid

echo "Step 5d"
stack run -- -r ./step5c.fluid -n identify-impossibles -a 'decl=eval' > step5d.fluid
stack run -- -c ./step5d.fluid

# Manual: fill holes
echo "Step 6"
stack run -- -c ./step6.fluid

echo "Step 7a"
stack run -- -r ./step6.fluid -n add-param -a 'func=lookupVar, index=0, type=`List Nat`, name=patV2' > step7a.fluid
stack run -- -c ./step7a.fluid

# Manual: fill holes
echo "Step 7b"
stack run -- -c ./step7b.fluid

echo "Step 7c"
stack run -- -r ./step7b.fluid -n rel-func-params -a 'func=lookupVar, inds=[1,4,5], reln=`Unzip`' > step7c.fluid
stack run -- -c ./step7c.fluid

# Broken: pattern expansion
# Not meant to typecheck because of impossible cases
echo "Step 7d"
# stack run -- -c ./step7d.fluid

echo "Step 7e"
stack run -- -r ./step7d.fluid -n identify-impossibles -a 'decl=lookupVar' > step7e.fluid
stack run -- -c ./step7e.fluid

# Manual: fill holes
echo "Step 7f"
stack run -- -c ./step7f.fluid

# Temporary to check bool tautology removal:
# stack run -- -r ./boolean-tautology.fluid -n rm-taut -a 'lx=35, ly=64, op=isEqual' > boolean-tautology2.fluid
# stack run -- -c ./boolean-tautology2.fluid
