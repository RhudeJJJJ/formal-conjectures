/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4614 : Family 10 := level10.get ⟨644,by decide⟩
def sourceMap4614 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4614 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4614_checked : acceptsGraphIso
    (source (graph core4614) (root 10) 2 2) DegreeTwoThreeSpectrum7303.graph sourceMap4614=true := by decide +kernel
theorem fusedMap4614_checked : acceptsGraphIso
    (fused (graph core4614) (root 10) 2 2) DegreeTwoThreeSpectrum5342.graph fusedMap4614=true := by decide +kernel
theorem certified4614 : Certified (graph core4614) (root 10) 2 2 :=
  of_native_maps core4614 DegreeTwoThreeSpectrum7303.graph DegreeTwoThreeSpectrum5342.graph
    sourceMap4614 fusedMap4614 sourceMap4614_checked fusedMap4614_checked
    DegreeTwoThreeFiniteComparisons.comparison4614
#print axioms sourceMap4614_checked
#print axioms fusedMap4614_checked
#print axioms certified4614
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
