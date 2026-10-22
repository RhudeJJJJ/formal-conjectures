/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4387 : Family 9 := level9.get ⟨567,by decide⟩
def sourceMap4387 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4387 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4387_checked : acceptsGraphIso
    (source (graph core4387) (root 9) 2 2) DegreeTwoThreeSpectrum4914.graph sourceMap4387=true := by decide +kernel
theorem fusedMap4387_checked : acceptsGraphIso
    (fused (graph core4387) (root 9) 2 2) DegreeTwoThreeSpectrum4211.graph fusedMap4387=true := by decide +kernel
theorem certified4387 : Certified (graph core4387) (root 9) 2 2 :=
  of_native_maps core4387 DegreeTwoThreeSpectrum4914.graph DegreeTwoThreeSpectrum4211.graph
    sourceMap4387 fusedMap4387 sourceMap4387_checked fusedMap4387_checked
    DegreeTwoThreeFiniteComparisons.comparison4387
#print axioms sourceMap4387_checked
#print axioms fusedMap4387_checked
#print axioms certified4387
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
