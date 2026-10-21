/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2424 : Family 10 := level10.get ⟨1317,by decide⟩
def sourceMap2424 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2424 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2424_checked : acceptsGraphIso
    (source (graph core2424) (root 10) 0 0) DegreeOneSmallSpectrum1947.graph sourceMap2424=true := by decide +kernel
theorem fusedMap2424_checked : acceptsGraphIso
    (fused (graph core2424) (root 10) 0 0) DegreeOneSmallSpectrum1946.graph fusedMap2424=true := by decide +kernel
theorem certified2424 : Certified (graph core2424) (root 10) 0 0 :=
  of_native_maps core2424 DegreeOneSmallSpectrum1947.graph DegreeOneSmallSpectrum1946.graph
    sourceMap2424 fusedMap2424 sourceMap2424_checked fusedMap2424_checked
    DegreeOneSmallComparisons.comparison2424
#print axioms sourceMap2424_checked
#print axioms fusedMap2424_checked
#print axioms certified2424
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
