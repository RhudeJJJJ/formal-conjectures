/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4105 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap4105 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4105 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4105_checked : acceptsGraphIso
    (source (graph core4105) (root 8) 2 2) DegreeTwoThreeSpectrum3268.graph sourceMap4105=true := by decide +kernel
theorem fusedMap4105_checked : acceptsGraphIso
    (fused (graph core4105) (root 8) 2 2) DegreeTwoThreeSpectrum2325.graph fusedMap4105=true := by decide +kernel
theorem certified4105 : Certified (graph core4105) (root 8) 2 2 :=
  of_native_maps core4105 DegreeTwoThreeSpectrum3268.graph DegreeTwoThreeSpectrum2325.graph
    sourceMap4105 fusedMap4105 sourceMap4105_checked fusedMap4105_checked
    DegreeTwoThreeFiniteComparisons.comparison4105
#print axioms sourceMap4105_checked
#print axioms fusedMap4105_checked
#print axioms certified4105
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
