/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4275 : Family 9 := level9.get ⟨284,by decide⟩
def sourceMap4275 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4275 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4275_checked : acceptsGraphIso
    (source (graph core4275) (root 9) 2 2) DegreeTwoThreeSpectrum4871.graph sourceMap4275=true := by decide +kernel
theorem fusedMap4275_checked : acceptsGraphIso
    (fused (graph core4275) (root 9) 2 2) DegreeTwoThreeSpectrum4105.graph fusedMap4275=true := by decide +kernel
theorem certified4275 : Certified (graph core4275) (root 9) 2 2 :=
  of_native_maps core4275 DegreeTwoThreeSpectrum4871.graph DegreeTwoThreeSpectrum4105.graph
    sourceMap4275 fusedMap4275 sourceMap4275_checked fusedMap4275_checked
    DegreeTwoThreeFiniteComparisons.comparison4275
#print axioms sourceMap4275_checked
#print axioms fusedMap4275_checked
#print axioms certified4275
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
