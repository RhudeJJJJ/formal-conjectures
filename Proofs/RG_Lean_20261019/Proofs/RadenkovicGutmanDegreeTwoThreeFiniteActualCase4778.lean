/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4778 : Family 10 := level10.get ⟨1078,by decide⟩
def sourceMap4778 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4778 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4778_checked : acceptsGraphIso
    (source (graph core4778) (root 10) 2 2) DegreeTwoThreeSpectrum7158.graph sourceMap4778=true := by decide +kernel
theorem fusedMap4778_checked : acceptsGraphIso
    (fused (graph core4778) (root 10) 2 2) DegreeTwoThreeSpectrum6139.graph fusedMap4778=true := by decide +kernel
theorem certified4778 : Certified (graph core4778) (root 10) 2 2 :=
  of_native_maps core4778 DegreeTwoThreeSpectrum7158.graph DegreeTwoThreeSpectrum6139.graph
    sourceMap4778 fusedMap4778 sourceMap4778_checked fusedMap4778_checked
    DegreeTwoThreeFiniteComparisons.comparison4778
#print axioms sourceMap4778_checked
#print axioms fusedMap4778_checked
#print axioms certified4778
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
