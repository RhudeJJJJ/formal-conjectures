/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2029 : Family 10 := level10.get ⟨381,by decide⟩
def sourceMap2029 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2029 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2029_checked : acceptsGraphIso
    (source (graph core2029) (root 10) 0 0) DegreeOneSmallSpectrum1208.graph sourceMap2029=true := by decide +kernel
theorem fusedMap2029_checked : acceptsGraphIso
    (fused (graph core2029) (root 10) 0 0) DegreeOneSmallSpectrum1490.graph fusedMap2029=true := by decide +kernel
theorem certified2029 : Certified (graph core2029) (root 10) 0 0 :=
  of_native_maps core2029 DegreeOneSmallSpectrum1208.graph DegreeOneSmallSpectrum1490.graph
    sourceMap2029 fusedMap2029 sourceMap2029_checked fusedMap2029_checked
    DegreeOneSmallComparisons.comparison2029
#print axioms sourceMap2029_checked
#print axioms fusedMap2029_checked
#print axioms certified2029
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
