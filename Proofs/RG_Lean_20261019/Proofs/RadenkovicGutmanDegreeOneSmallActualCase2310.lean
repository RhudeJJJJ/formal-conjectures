/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2310 : Family 10 := level10.get ⟨996,by decide⟩
def sourceMap2310 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2310 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2310_checked : acceptsGraphIso
    (source (graph core2310) (root 10) 0 0) DegreeOneSmallSpectrum1524.graph sourceMap2310=true := by decide +kernel
theorem fusedMap2310_checked : acceptsGraphIso
    (fused (graph core2310) (root 10) 0 0) DegreeOneSmallSpectrum1526.graph fusedMap2310=true := by decide +kernel
theorem certified2310 : Certified (graph core2310) (root 10) 0 0 :=
  of_native_maps core2310 DegreeOneSmallSpectrum1524.graph DegreeOneSmallSpectrum1526.graph
    sourceMap2310 fusedMap2310 sourceMap2310_checked fusedMap2310_checked
    DegreeOneSmallComparisons.comparison2310
#print axioms sourceMap2310_checked
#print axioms fusedMap2310_checked
#print axioms certified2310
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
