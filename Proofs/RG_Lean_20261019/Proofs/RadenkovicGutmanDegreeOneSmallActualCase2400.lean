/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2400 : Family 10 := level10.get ⟨1245,by decide⟩
def sourceMap2400 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2400 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2400_checked : acceptsGraphIso
    (source (graph core2400) (root 10) 0 0) DegreeOneSmallSpectrum1798.graph sourceMap2400=true := by decide +kernel
theorem fusedMap2400_checked : acceptsGraphIso
    (fused (graph core2400) (root 10) 0 0) DegreeOneSmallSpectrum1897.graph fusedMap2400=true := by decide +kernel
theorem certified2400 : Certified (graph core2400) (root 10) 0 0 :=
  of_native_maps core2400 DegreeOneSmallSpectrum1798.graph DegreeOneSmallSpectrum1897.graph
    sourceMap2400 fusedMap2400 sourceMap2400_checked fusedMap2400_checked
    DegreeOneSmallComparisons.comparison2400
#print axioms sourceMap2400_checked
#print axioms fusedMap2400_checked
#print axioms certified2400
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
