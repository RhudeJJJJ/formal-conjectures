/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2220 : Family 10 := level10.get ⟨747,by decide⟩
def sourceMap2220 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2220 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2220_checked : acceptsGraphIso
    (source (graph core2220) (root 10) 0 0) DegreeOneSmallSpectrum1804.graph sourceMap2220=true := by decide +kernel
theorem fusedMap2220_checked : acceptsGraphIso
    (fused (graph core2220) (root 10) 0 0) DegreeOneSmallSpectrum1378.graph fusedMap2220=true := by decide +kernel
theorem certified2220 : Certified (graph core2220) (root 10) 0 0 :=
  of_native_maps core2220 DegreeOneSmallSpectrum1804.graph DegreeOneSmallSpectrum1378.graph
    sourceMap2220 fusedMap2220 sourceMap2220_checked fusedMap2220_checked
    DegreeOneSmallComparisons.comparison2220
#print axioms sourceMap2220_checked
#print axioms fusedMap2220_checked
#print axioms certified2220
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
