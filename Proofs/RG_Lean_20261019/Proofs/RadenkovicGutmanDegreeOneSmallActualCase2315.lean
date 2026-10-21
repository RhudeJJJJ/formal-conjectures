/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2315 : Family 10 := level10.get ⟨1003,by decide⟩
def sourceMap2315 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2315 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2315_checked : acceptsGraphIso
    (source (graph core2315) (root 10) 0 0) DegreeOneSmallSpectrum1546.graph sourceMap2315=true := by decide +kernel
theorem fusedMap2315_checked : acceptsGraphIso
    (fused (graph core2315) (root 10) 0 0) DegreeOneSmallSpectrum1552.graph fusedMap2315=true := by decide +kernel
theorem certified2315 : Certified (graph core2315) (root 10) 0 0 :=
  of_native_maps core2315 DegreeOneSmallSpectrum1546.graph DegreeOneSmallSpectrum1552.graph
    sourceMap2315 fusedMap2315 sourceMap2315_checked fusedMap2315_checked
    DegreeOneSmallComparisons.comparison2315
#print axioms sourceMap2315_checked
#print axioms fusedMap2315_checked
#print axioms certified2315
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
