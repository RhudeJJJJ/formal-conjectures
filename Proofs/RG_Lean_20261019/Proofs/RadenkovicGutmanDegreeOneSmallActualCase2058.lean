/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2058 : Family 10 := level10.get ⟨432,by decide⟩
def sourceMap2058 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2058 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2058_checked : acceptsGraphIso
    (source (graph core2058) (root 10) 0 0) DegreeOneSmallSpectrum1136.graph sourceMap2058=true := by decide +kernel
theorem fusedMap2058_checked : acceptsGraphIso
    (fused (graph core2058) (root 10) 0 0) DegreeOneSmallSpectrum1504.graph fusedMap2058=true := by decide +kernel
theorem certified2058 : Certified (graph core2058) (root 10) 0 0 :=
  of_native_maps core2058 DegreeOneSmallSpectrum1136.graph DegreeOneSmallSpectrum1504.graph
    sourceMap2058 fusedMap2058 sourceMap2058_checked fusedMap2058_checked
    DegreeOneSmallComparisons.comparison2058
#print axioms sourceMap2058_checked
#print axioms fusedMap2058_checked
#print axioms certified2058
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
