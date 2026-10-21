/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2006 : Family 10 := level10.get ⟨342,by decide⟩
def sourceMap2006 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2006 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2006_checked : acceptsGraphIso
    (source (graph core2006) (root 10) 0 0) DegreeOneSmallSpectrum1187.graph sourceMap2006=true := by decide +kernel
theorem fusedMap2006_checked : acceptsGraphIso
    (fused (graph core2006) (root 10) 0 0) DegreeOneSmallSpectrum1452.graph fusedMap2006=true := by decide +kernel
theorem certified2006 : Certified (graph core2006) (root 10) 0 0 :=
  of_native_maps core2006 DegreeOneSmallSpectrum1187.graph DegreeOneSmallSpectrum1452.graph
    sourceMap2006 fusedMap2006 sourceMap2006_checked fusedMap2006_checked
    DegreeOneSmallComparisons.comparison2006
#print axioms sourceMap2006_checked
#print axioms fusedMap2006_checked
#print axioms certified2006
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
