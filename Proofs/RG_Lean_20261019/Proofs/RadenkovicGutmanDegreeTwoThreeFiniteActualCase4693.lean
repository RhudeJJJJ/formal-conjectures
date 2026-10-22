/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4693 : Family 10 := level10.get ⟨861,by decide⟩
def sourceMap4693 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4693 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4693_checked : acceptsGraphIso
    (source (graph core4693) (root 10) 2 2) DegreeTwoThreeSpectrum7507.graph sourceMap4693=true := by decide +kernel
theorem fusedMap4693_checked : acceptsGraphIso
    (fused (graph core4693) (root 10) 2 2) DegreeTwoThreeSpectrum5698.graph fusedMap4693=true := by decide +kernel
theorem certified4693 : Certified (graph core4693) (root 10) 2 2 :=
  of_native_maps core4693 DegreeTwoThreeSpectrum7507.graph DegreeTwoThreeSpectrum5698.graph
    sourceMap4693 fusedMap4693 sourceMap4693_checked fusedMap4693_checked
    DegreeTwoThreeFiniteComparisons.comparison4693
#print axioms sourceMap4693_checked
#print axioms fusedMap4693_checked
#print axioms certified4693
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
