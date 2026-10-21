/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2030 : Family 10 := level10.get ⟨382,by decide⟩
def sourceMap2030 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2030 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2030_checked : acceptsGraphIso
    (source (graph core2030) (root 10) 0 0) DegreeOneSmallSpectrum1223.graph sourceMap2030=true := by decide +kernel
theorem fusedMap2030_checked : acceptsGraphIso
    (fused (graph core2030) (root 10) 0 0) DegreeOneSmallSpectrum1491.graph fusedMap2030=true := by decide +kernel
theorem certified2030 : Certified (graph core2030) (root 10) 0 0 :=
  of_native_maps core2030 DegreeOneSmallSpectrum1223.graph DegreeOneSmallSpectrum1491.graph
    sourceMap2030 fusedMap2030 sourceMap2030_checked fusedMap2030_checked
    DegreeOneSmallComparisons.comparison2030
#print axioms sourceMap2030_checked
#print axioms fusedMap2030_checked
#print axioms certified2030
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
