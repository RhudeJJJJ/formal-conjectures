/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2047 : Family 10 := level10.get ⟨409,by decide⟩
def sourceMap2047 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2047 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2047_checked : acceptsGraphIso
    (source (graph core2047) (root 10) 0 0) DegreeOneSmallSpectrum1146.graph sourceMap2047=true := by decide +kernel
theorem fusedMap2047_checked : acceptsGraphIso
    (fused (graph core2047) (root 10) 0 0) DegreeOneSmallSpectrum1503.graph fusedMap2047=true := by decide +kernel
theorem certified2047 : Certified (graph core2047) (root 10) 0 0 :=
  of_native_maps core2047 DegreeOneSmallSpectrum1146.graph DegreeOneSmallSpectrum1503.graph
    sourceMap2047 fusedMap2047 sourceMap2047_checked fusedMap2047_checked
    DegreeOneSmallComparisons.comparison2047
#print axioms sourceMap2047_checked
#print axioms fusedMap2047_checked
#print axioms certified2047
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
