/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4336 : Family 9 := level9.get ⟨444,by decide⟩
def sourceMap4336 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4336 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4336_checked : acceptsGraphIso
    (source (graph core4336) (root 9) 2 2) DegreeTwoThreeSpectrum4821.graph sourceMap4336=true := by decide +kernel
theorem fusedMap4336_checked : acceptsGraphIso
    (fused (graph core4336) (root 9) 2 2) DegreeTwoThreeSpectrum4453.graph fusedMap4336=true := by decide +kernel
theorem certified4336 : Certified (graph core4336) (root 9) 2 2 :=
  of_native_maps core4336 DegreeTwoThreeSpectrum4821.graph DegreeTwoThreeSpectrum4453.graph
    sourceMap4336 fusedMap4336 sourceMap4336_checked fusedMap4336_checked
    DegreeTwoThreeFiniteComparisons.comparison4336
#print axioms sourceMap4336_checked
#print axioms fusedMap4336_checked
#print axioms certified4336
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
