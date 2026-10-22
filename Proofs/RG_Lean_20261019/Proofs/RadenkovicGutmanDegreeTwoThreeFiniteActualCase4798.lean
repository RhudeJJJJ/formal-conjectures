/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4798 : Family 10 := level10.get ⟨1128,by decide⟩
def sourceMap4798 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4798 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4798_checked : acceptsGraphIso
    (source (graph core4798) (root 10) 2 2) DegreeTwoThreeSpectrum7209.graph sourceMap4798=true := by decide +kernel
theorem fusedMap4798_checked : acceptsGraphIso
    (fused (graph core4798) (root 10) 2 2) DegreeTwoThreeSpectrum6242.graph fusedMap4798=true := by decide +kernel
theorem certified4798 : Certified (graph core4798) (root 10) 2 2 :=
  of_native_maps core4798 DegreeTwoThreeSpectrum7209.graph DegreeTwoThreeSpectrum6242.graph
    sourceMap4798 fusedMap4798 sourceMap4798_checked fusedMap4798_checked
    DegreeTwoThreeFiniteComparisons.comparison4798
#print axioms sourceMap4798_checked
#print axioms fusedMap4798_checked
#print axioms certified4798
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
