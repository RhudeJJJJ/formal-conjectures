/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2050 : Family 10 := level10.get ⟨416,by decide⟩
def sourceMap2050 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,1,0,8,9,10,11,12,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2050 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2050_checked : acceptsGraphIso
    (source (graph core2050) (root 10) 0 0) DegreeOneSmallSpectrum1474.graph sourceMap2050=true := by decide +kernel
theorem fusedMap2050_checked : acceptsGraphIso
    (fused (graph core2050) (root 10) 0 0) DegreeOneSmallSpectrum1462.graph fusedMap2050=true := by decide +kernel
theorem certified2050 : Certified (graph core2050) (root 10) 0 0 :=
  of_native_maps core2050 DegreeOneSmallSpectrum1474.graph DegreeOneSmallSpectrum1462.graph
    sourceMap2050 fusedMap2050 sourceMap2050_checked fusedMap2050_checked
    DegreeOneSmallComparisons.comparison2050
#print axioms sourceMap2050_checked
#print axioms fusedMap2050_checked
#print axioms certified2050
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
