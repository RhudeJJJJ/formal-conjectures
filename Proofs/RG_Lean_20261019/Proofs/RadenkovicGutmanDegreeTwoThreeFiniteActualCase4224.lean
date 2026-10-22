/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4224 : Family 9 := level9.get ⟨131,by decide⟩
def sourceMap4224 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,10,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4224 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 2 2 v)
theorem sourceMap4224_checked : acceptsGraphIso
    (source (graph core4224) (root 9) 2 2) DegreeTwoThreeSpectrum4541.graph sourceMap4224=true := by decide +kernel
theorem fusedMap4224_checked : acceptsGraphIso
    (fused (graph core4224) (root 9) 2 2) DegreeTwoThreeSpectrum4166.graph fusedMap4224=true := by decide +kernel
theorem certified4224 : Certified (graph core4224) (root 9) 2 2 :=
  of_native_maps core4224 DegreeTwoThreeSpectrum4541.graph DegreeTwoThreeSpectrum4166.graph
    sourceMap4224 fusedMap4224 sourceMap4224_checked fusedMap4224_checked
    DegreeTwoThreeFiniteComparisons.comparison4224
#print axioms sourceMap4224_checked
#print axioms fusedMap4224_checked
#print axioms certified4224
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
