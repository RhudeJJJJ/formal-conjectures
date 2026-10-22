/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4978 : Family 10 := level10.get ⟨1570,by decide⟩
def sourceMap4978 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4978 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4978_checked : acceptsGraphIso
    (source (graph core4978) (root 10) 2 2) DegreeTwoThreeSpectrum7579.graph sourceMap4978=true := by decide +kernel
theorem fusedMap4978_checked : acceptsGraphIso
    (fused (graph core4978) (root 10) 2 2) DegreeTwoThreeSpectrum6048.graph fusedMap4978=true := by decide +kernel
theorem certified4978 : Certified (graph core4978) (root 10) 2 2 :=
  of_native_maps core4978 DegreeTwoThreeSpectrum7579.graph DegreeTwoThreeSpectrum6048.graph
    sourceMap4978 fusedMap4978 sourceMap4978_checked fusedMap4978_checked
    DegreeTwoThreeFiniteComparisons.comparison4978
#print axioms sourceMap4978_checked
#print axioms fusedMap4978_checked
#print axioms certified4978
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
