/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4158 : Family 8 := level8.get ⟨183,by decide⟩
def sourceMap4158 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,7,8,9,10,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4158 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4158_checked : acceptsGraphIso
    (source (graph core4158) (root 8) 2 2) DegreeTwoThreeSpectrum3612.graph sourceMap4158=true := by decide +kernel
theorem fusedMap4158_checked : acceptsGraphIso
    (fused (graph core4158) (root 8) 2 2) DegreeTwoThreeSpectrum2964.graph fusedMap4158=true := by decide +kernel
theorem certified4158 : Certified (graph core4158) (root 8) 2 2 :=
  of_native_maps core4158 DegreeTwoThreeSpectrum3612.graph DegreeTwoThreeSpectrum2964.graph
    sourceMap4158 fusedMap4158 sourceMap4158_checked fusedMap4158_checked
    DegreeTwoThreeFiniteComparisons.comparison4158
#print axioms sourceMap4158_checked
#print axioms fusedMap4158_checked
#print axioms certified4158
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
