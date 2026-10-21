/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2131 : Family 10 := level10.get ⟨572,by decide⟩
def sourceMap2131 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2131 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2131_checked : acceptsGraphIso
    (source (graph core2131) (root 10) 0 0) DegreeOneSmallSpectrum1755.graph sourceMap2131=true := by decide +kernel
theorem fusedMap2131_checked : acceptsGraphIso
    (fused (graph core2131) (root 10) 0 0) DegreeOneSmallSpectrum1109.graph fusedMap2131=true := by decide +kernel
theorem certified2131 : Certified (graph core2131) (root 10) 0 0 :=
  of_native_maps core2131 DegreeOneSmallSpectrum1755.graph DegreeOneSmallSpectrum1109.graph
    sourceMap2131 fusedMap2131 sourceMap2131_checked fusedMap2131_checked
    DegreeOneSmallComparisons.comparison2131
#print axioms sourceMap2131_checked
#print axioms fusedMap2131_checked
#print axioms certified2131
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
