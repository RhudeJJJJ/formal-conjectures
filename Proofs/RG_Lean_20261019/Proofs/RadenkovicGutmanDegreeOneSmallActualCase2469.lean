/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2469 : Family 10 := level10.get ⟨1568,by decide⟩
def sourceMap2469 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (sourceLabel 10 0 0 v)
def fusedMap2469 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2469_checked : acceptsGraphIso
    (source (graph core2469) (root 10) 0 0) DegreeOneSmallSpectrum2004.graph sourceMap2469=true := by decide +kernel
theorem fusedMap2469_checked : acceptsGraphIso
    (fused (graph core2469) (root 10) 0 0) DegreeOneSmallSpectrum1605.graph fusedMap2469=true := by decide +kernel
theorem certified2469 : Certified (graph core2469) (root 10) 0 0 :=
  of_native_maps core2469 DegreeOneSmallSpectrum2004.graph DegreeOneSmallSpectrum1605.graph
    sourceMap2469 fusedMap2469 sourceMap2469_checked fusedMap2469_checked
    DegreeOneSmallComparisons.comparison2469
#print axioms sourceMap2469_checked
#print axioms fusedMap2469_checked
#print axioms certified2469
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
