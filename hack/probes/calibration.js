const api = require('../load-model.js')(process.argv[2]);
const M = api.MODEL, I = M.interpret(api.FIXTURE), K = I.keys;
const a = ['companies','A'], b = [...a,'teams','B'], c = [...a,'teams','C'], w1 = [...b,'widgets','w1'];
const show = (l, v) => console.log(l.padEnd(58), JSON.stringify(v));
const guarded = M.interpret(api.FIXTURE, { fieldGuards: true });
show('C5 setOwner registered in Core', Boolean(K['widgets.setOwner']));
show('C5 setOwner patterns with Field Guards', guarded.keys['widgets.setOwner'].patterns.map(p => p.join('/')));
// D1: permits at A and B for widgets.get (viewer), forbid at C; project at A, grant-shaped
const rules = M.rulesFromGrants([{scope:a,selectors:api.ROLES.viewer},{scope:b,selectors:api.ROLES.viewer},{scope:c,selectors:api.ROLES.viewer,effect:'forbid'}], K);
const readClaims = (anchor, profile) => M.projectContext(rules, K, anchor, { profile }).claims.filter(c => c.key === 'widgets.get');
const sc = readClaims(a, 'SCOPED_CLAIMS');
show('D1 scoped claims widgets.get @A', sc.map(x=>[x.kind,x.path.join('/'),x.holes.map(h=>h.join('/'))]));
show('D1 grant-shaped widgets.get @A', readClaims(a, 'GRANT_SHAPED').map(x => [x.kind, x.path.join('/')]));
show('D1 grant-shaped @root', readClaims([], 'GRANT_SHAPED').map(x => [x.kind, x.path.join('/')]));
// E1: all-conditional custom method
const F2 = {...api.FIXTURE, methods:[...api.FIXTURE.methods,{name:'PokeWidget',authz:{requirements:[{accessClass:'EXECUTE',operation:'poke',condition:'force'}]},request:{name:{type:'Widget'},force:true}}]};
const I2 = M.interpret(F2); show('E1 build errors', I2.errors);
show('E1 decide force=false (no grants)', M.decideRequest([], I2, 'PokeWidget', {name:w1, force:false}));
// C6
const F3 = {...api.FIXTURE, methods:[...api.FIXTURE.methods,{name:'NukeWidget',authz:{requirements:[{accessClass:'DELETE',operation:'nuke'}]},noSideEffects:true,request:{name:{type:'Widget'}}}]};
const I3 = M.interpret(F3);
show('C6 NO_SIDE_EFFECTS+DELETE', { registered: Boolean(I3.methods.NukeWidget), errors: I3.errors });
// E2: wildcard search with no grants at all
show('E2 wildcard Search, zero grants, filtering handler', M.authorizeRequest([], I, 'SearchWidgets', {parent:[...a,'teams','-']}, { handlerResolvesResiduals: true }));
// E3: empty BatchGet under root admin
const admin = M.rulesFromGrants([{scope:[],selectors:api.ROLES.admin}], K);
show('E3 empty BatchGet with no parent under root admin', M.batchRequestStatus(admin, I, 'BatchGetWidgets', {'names[]':[]}));
show('E3 empty BatchGet with parent B under root admin', M.batchRequestStatus(admin, I, 'BatchGetWidgets', {parent:b, 'names[]':[]}));
// A3 (post-fix) malformed names
show('A3 GetWidget with a team name under root admin', M.decideRequest(admin, I, 'GetWidget', {name:b}));
// V6 offer ceiling: InspectAccessPolicy effect
show('V6 InspectAccessPolicy effect', I.methods.InspectAccessPolicy.effect);
show('V6 InspectAccessPolicy under a read-only ceiling', M.methodAvailable(I, 'InspectAccessPolicy', { readOnlyCredential: true }));
// Wildcard on Create
show('C7 Create with wildcard parent (admin)', M.decideRequest(admin, I, 'CreateWidget', {parent:[...a,'teams','-'], populated:[]}));
const F4 = {...api.FIXTURE, methods: api.FIXTURE.methods.map(m=>m.name==='CreateWidget'?{...m,authz:{standard:{wildcardVariables:['team']}}}:m)};
const I4 = M.interpret(F4); show('C7 Create declaring wildcard_variables: errors', I4.errors);
show('C7 ...then decide wildcard Create (admin)', M.decideRequest(admin, I4, 'CreateWidget', {parent:[...a,'teams','-'], populated:[]}));
// BatchList
const F5 = {...api.FIXTURE, methods:[...api.FIXTURE.methods,{name:'BatchListWidgets',authz:{standard:{}},request:{parent:{childType:'Widget'}}}]};
show('C7 BatchListWidgets accepted? errors', M.interpret(F5).errors);
// queryAnchors canSee on canonical
show('D8 queryAnchors canonical with canSee=false', M.queryAnchors([{name:'companies/A'}], s=>s.name, ()=>false, name => M.isResourceName(Object.values(K).flatMap(k => k.patterns), name.split('/'))));
