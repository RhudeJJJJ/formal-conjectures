/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2137 : Family 10 := level10.get ⟨582,by decide⟩
def sourceMap2137 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2137 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2137_checked : acceptsGraphIso
    (source (graph core2137) (root 10) 0 0) DegreeOneSmallSpectrum1797.graph sourceMap2137=true := by decide +kernel
theorem fusedMap2137_checked : acceptsGraphIso
    (fused (graph core2137) (root 10) 0 0) DegreeOneSmallSpectrum1120.graph fusedMap2137=true := by decide +kernel
theorem certified2137 : Certified (graph core2137) (root 10) 0 0 :=
  of_native_maps core2137 DegreeOneSmallSpectrum1797.graph DegreeOneSmallSpectrum1120.graph
    sourceMap2137 fusedMap2137 sourceMap2137_checked fusedMap2137_checked
    DegreeOneSmallComparisons.comparison2137
#print axioms sourceMap2137_checked
#print axioms fusedMap2137_checked
#print axioms certified2137
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
