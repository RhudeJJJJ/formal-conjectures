/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2401 : Family 10 := level10.get ⟨1249,by decide⟩
def sourceMap2401 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2401 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2401_checked : acceptsGraphIso
    (source (graph core2401) (root 10) 0 0) DegreeOneSmallSpectrum1851.graph sourceMap2401=true := by decide +kernel
theorem fusedMap2401_checked : acceptsGraphIso
    (fused (graph core2401) (root 10) 0 0) DegreeOneSmallSpectrum1900.graph fusedMap2401=true := by decide +kernel
theorem certified2401 : Certified (graph core2401) (root 10) 0 0 :=
  of_native_maps core2401 DegreeOneSmallSpectrum1851.graph DegreeOneSmallSpectrum1900.graph
    sourceMap2401 fusedMap2401 sourceMap2401_checked fusedMap2401_checked
    DegreeOneSmallComparisons.comparison2401
#print axioms sourceMap2401_checked
#print axioms fusedMap2401_checked
#print axioms certified2401
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
