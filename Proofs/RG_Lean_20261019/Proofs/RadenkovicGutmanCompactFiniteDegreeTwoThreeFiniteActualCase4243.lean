/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4243 : Family 9 := level9.get ⟨193,by decide⟩
def sourceMap4243 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,15,13,14,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4243 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4243_checked : acceptsGraphIso
    (source (graph core4243) (root 9) 2 2) DegreeTwoThreeSpectrum4785.graph sourceMap4243=true := by decide +kernel
theorem fusedMap4243_checked : acceptsGraphIso
    (fused (graph core4243) (root 9) 2 2) DegreeTwoThreeSpectrum3966.graph fusedMap4243=true := by decide +kernel
theorem certified4243 : Certified (graph core4243) (root 9) 2 2 :=
  of_native_maps core4243 DegreeTwoThreeSpectrum4785.graph DegreeTwoThreeSpectrum3966.graph
    sourceMap4243 fusedMap4243 sourceMap4243_checked fusedMap4243_checked
    DegreeTwoThreeFiniteComparisons.comparison4243
#print axioms sourceMap4243_checked
#print axioms fusedMap4243_checked
#print axioms certified4243
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
