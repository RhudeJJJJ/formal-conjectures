/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4388 : Family 9 := level9.get ⟨570,by decide⟩
def sourceMap4388 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4388 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4388_checked : acceptsGraphIso
    (source (graph core4388) (root 9) 2 2) DegreeTwoThreeSpectrum4915.graph sourceMap4388=true := by decide +kernel
theorem fusedMap4388_checked : acceptsGraphIso
    (fused (graph core4388) (root 9) 2 2) DegreeTwoThreeSpectrum4216.graph fusedMap4388=true := by decide +kernel
theorem certified4388 : Certified (graph core4388) (root 9) 2 2 :=
  of_native_maps core4388 DegreeTwoThreeSpectrum4915.graph DegreeTwoThreeSpectrum4216.graph
    sourceMap4388 fusedMap4388 sourceMap4388_checked fusedMap4388_checked
    DegreeTwoThreeFiniteComparisons.comparison4388
#print axioms sourceMap4388_checked
#print axioms fusedMap4388_checked
#print axioms certified4388
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
