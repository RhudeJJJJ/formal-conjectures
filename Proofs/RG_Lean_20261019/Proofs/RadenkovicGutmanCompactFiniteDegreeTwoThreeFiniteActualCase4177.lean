/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4177 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap4177 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4177 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4177_checked : acceptsGraphIso
    (source (graph core4177) (root 8) 2 2) DegreeTwoThreeSpectrum3821.graph sourceMap4177=true := by decide +kernel
theorem fusedMap4177_checked : acceptsGraphIso
    (fused (graph core4177) (root 8) 2 2) DegreeTwoThreeSpectrum2646.graph fusedMap4177=true := by decide +kernel
theorem certified4177 : Certified (graph core4177) (root 8) 2 2 :=
  of_native_maps core4177 DegreeTwoThreeSpectrum3821.graph DegreeTwoThreeSpectrum2646.graph
    sourceMap4177 fusedMap4177 sourceMap4177_checked fusedMap4177_checked
    DegreeTwoThreeFiniteComparisons.comparison4177
#print axioms sourceMap4177_checked
#print axioms fusedMap4177_checked
#print axioms certified4177
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
