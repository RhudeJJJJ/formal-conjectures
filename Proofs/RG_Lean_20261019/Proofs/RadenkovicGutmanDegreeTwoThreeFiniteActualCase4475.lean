/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4475 : Family 10 := level10.get ⟨194,by decide⟩
def sourceMap4475 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4475 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4475_checked : acceptsGraphIso
    (source (graph core4475) (root 10) 2 2) DegreeTwoThreeSpectrum6043.graph sourceMap4475=true := by decide +kernel
theorem fusedMap4475_checked : acceptsGraphIso
    (fused (graph core4475) (root 10) 2 2) DegreeTwoThreeSpectrum5158.graph fusedMap4475=true := by decide +kernel
theorem certified4475 : Certified (graph core4475) (root 10) 2 2 :=
  of_native_maps core4475 DegreeTwoThreeSpectrum6043.graph DegreeTwoThreeSpectrum5158.graph
    sourceMap4475 fusedMap4475 sourceMap4475_checked fusedMap4475_checked
    DegreeTwoThreeFiniteComparisons.comparison4475
#print axioms sourceMap4475_checked
#print axioms fusedMap4475_checked
#print axioms certified4475
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
