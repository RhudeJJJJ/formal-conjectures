/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2320 : Family 10 := level10.get ⟨1012,by decide⟩
def sourceMap2320 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2320 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2320_checked : acceptsGraphIso
    (source (graph core2320) (root 10) 0 0) DegreeOneSmallSpectrum1570.graph sourceMap2320=true := by decide +kernel
theorem fusedMap2320_checked : acceptsGraphIso
    (fused (graph core2320) (root 10) 0 0) DegreeOneSmallSpectrum1572.graph fusedMap2320=true := by decide +kernel
theorem certified2320 : Certified (graph core2320) (root 10) 0 0 :=
  of_native_maps core2320 DegreeOneSmallSpectrum1570.graph DegreeOneSmallSpectrum1572.graph
    sourceMap2320 fusedMap2320 sourceMap2320_checked fusedMap2320_checked
    DegreeOneSmallComparisons.comparison2320
#print axioms sourceMap2320_checked
#print axioms fusedMap2320_checked
#print axioms certified2320
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
