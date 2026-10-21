/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2434 : Family 10 := level10.get ⟨1352,by decide⟩
def sourceMap2434 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2434 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2434_checked : acceptsGraphIso
    (source (graph core2434) (root 10) 0 0) DegreeOneSmallSpectrum1557.graph sourceMap2434=true := by decide +kernel
theorem fusedMap2434_checked : acceptsGraphIso
    (fused (graph core2434) (root 10) 0 0) DegreeOneSmallSpectrum1965.graph fusedMap2434=true := by decide +kernel
theorem certified2434 : Certified (graph core2434) (root 10) 0 0 :=
  of_native_maps core2434 DegreeOneSmallSpectrum1557.graph DegreeOneSmallSpectrum1965.graph
    sourceMap2434 fusedMap2434 sourceMap2434_checked fusedMap2434_checked
    DegreeOneSmallComparisons.comparison2434
#print axioms sourceMap2434_checked
#print axioms fusedMap2434_checked
#print axioms certified2434
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
