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

echo "Step 3c"
# Does not typecheck because of impossible cases (intended)
stack run -- -r ./step3b.fluid -n expand-pattern -a 'func=lookupVar, index=0' > step3b1.fluid
stack run -- -r ./step3b1.fluid -n expand-pattern -a 'func=lookupVar, index=2' > step3c.fluid

echo "Step 3d"
stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

# Manual: fill holes + remove case expression
echo "Step 4"
stack run -- -c ./step4.fluid

echo "Step 5a"
stack run -- -r ./step4.fluid -n add-param -a 'func=eval, index=0, type=`List Nat`, name=patV1' > step5a.fluid
stack run -- -c ./step5a.fluid

echo "Step 5b"
stack run -- -r ./step5a.fluid -n rel-func-params -a 'func=eval, inds=[3,2,4], reln=`Unzip`' > step5b.fluid
stack run -- -c ./step5b.fluid

# Pattern expansion
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
stack run -- -r ./step5c8.fluid -n expand-pattern-single -a 'pos=55:16, name=x' > step5c9.fluid

echo 'step5c9'
stack run -- -r ./step5c9.fluid -n expand-pattern-single -a 'pos=55:88, name=p' > step5c10.fluid
stack run -- -r ./step5c10.fluid -n identify-impossibles -a 'decl=eval' > step5c.fluid

echo "Step 5d"
stack run -- -r ./step5c.fluid -n identify-impossibles -a 'decl=eval' > step5d.fluid
stack run -- -c ./step5d.fluid

# Manual: fill holes
echo "Step 6"
stack run -- -c ./step6.fluid

echo "Step 7a"
stack run -- -r ./step6.fluid -n add-param -a 'func=lookupVar, index=0, type=`List Nat`, name=patV2' > step7a.fluid
stack run -- -c ./step7a.fluid

# Pattern expansion
echo "Step 7b"
stack run -- -r ./step7a.fluid -n expand-pattern-single -a "pos=38:11, name=q" > step7b.fluid
stack run -- -c ./step7b.fluid

# Manual: fill holes
echo "Step 7c"
stack run -- -c ./step7c.fluid

echo "Step 7d"
stack run -- -r ./step7c.fluid -n rel-func-params -a 'func=lookupVar, inds=[1,4,5], reln=`Unzip`' > step7d.fluid
stack run -- -c ./step7d.fluid

# Pattern expansion
# Not meant to typecheck because of impossible cases
echo "Step 7e"
stack run -- -r ./step7d.fluid -n expand-pattern -a "func=lookupVar, index=5" > step7e1.fluid
stack run -- -r ./step7e1.fluid -n identify-impossibles -a 'decl=lookupVar' > step7e.fluid
stack run -- -c ./step7e.fluid

echo "Step 7f"
stack run -- -r ./step7e.fluid -n identify-impossibles -a 'decl=lookupVar' > step7f.fluid
stack run -- -c ./step7f.fluid

# Manual: fill holes + remove impossible case (we could add an extra expansion here l130-131)
echo "Step 8"
stack run -- -c ./step8.fluid

# Remove maybe
echo "Step 9"
stack run -- -r ./step8.fluid -n remove-maybe -a 'func=lookupVar' > step9.fluid
stack run -- -c ./step9.fluid

# Step 10 not needed anymore

# Remove maybe
echo "Step 11"
stack run -- -r ./step9.fluid -n remove-maybe -a 'func=eval' > step11.fluid
stack run -- -c ./step11.fluid
