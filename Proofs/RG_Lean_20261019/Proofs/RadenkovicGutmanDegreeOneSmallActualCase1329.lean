/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1329 : Family 9 := level9.get ⟨86,by decide⟩
def sourceMap1329 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1329 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1329_checked : acceptsGraphIso
    (source (graph core1329) (root 9) 0 0) DegreeOneSmallSpectrum444.graph sourceMap1329=true := by decide +kernel
theorem fusedMap1329_checked : acceptsGraphIso
    (fused (graph core1329) (root 9) 0 0) DegreeOneSmallSpectrum558.graph fusedMap1329=true := by decide +kernel
theorem certified1329 : Certified (graph core1329) (root 9) 0 0 :=
  of_native_maps core1329 DegreeOneSmallSpectrum444.graph DegreeOneSmallSpectrum558.graph
    sourceMap1329 fusedMap1329 sourceMap1329_checked fusedMap1329_checked
    DegreeOneSmallComparisons.comparison1329
#print axioms sourceMap1329_checked
#print axioms fusedMap1329_checked
#print axioms certified1329
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
