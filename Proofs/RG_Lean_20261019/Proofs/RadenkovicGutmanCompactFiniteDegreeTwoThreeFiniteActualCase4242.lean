/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4242 : Family 9 := level9.get ⟨192,by decide⟩
def sourceMap4242 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,14,15,13,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4242 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4242_checked : acceptsGraphIso
    (source (graph core4242) (root 9) 2 2) DegreeTwoThreeSpectrum4787.graph sourceMap4242=true := by decide +kernel
theorem fusedMap4242_checked : acceptsGraphIso
    (fused (graph core4242) (root 9) 2 2) DegreeTwoThreeSpectrum3964.graph fusedMap4242=true := by decide +kernel
theorem certified4242 : Certified (graph core4242) (root 9) 2 2 :=
  of_native_maps core4242 DegreeTwoThreeSpectrum4787.graph DegreeTwoThreeSpectrum3964.graph
    sourceMap4242 fusedMap4242 sourceMap4242_checked fusedMap4242_checked
    DegreeTwoThreeFiniteComparisons.comparison4242
#print axioms sourceMap4242_checked
#print axioms fusedMap4242_checked
#print axioms certified4242
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
