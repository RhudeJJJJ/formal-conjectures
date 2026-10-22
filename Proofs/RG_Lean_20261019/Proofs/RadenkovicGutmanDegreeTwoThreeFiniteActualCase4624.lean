/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4624 : Family 10 := level10.get ⟨668,by decide⟩
def sourceMap4624 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,15,16,13,14,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4624 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4624_checked : acceptsGraphIso
    (source (graph core4624) (root 10) 2 2) DegreeTwoThreeSpectrum7316.graph sourceMap4624=true := by decide +kernel
theorem fusedMap4624_checked : acceptsGraphIso
    (fused (graph core4624) (root 10) 2 2) DegreeTwoThreeSpectrum5380.graph fusedMap4624=true := by decide +kernel
theorem certified4624 : Certified (graph core4624) (root 10) 2 2 :=
  of_native_maps core4624 DegreeTwoThreeSpectrum7316.graph DegreeTwoThreeSpectrum5380.graph
    sourceMap4624 fusedMap4624 sourceMap4624_checked fusedMap4624_checked
    DegreeTwoThreeFiniteComparisons.comparison4624
#print axioms sourceMap4624_checked
#print axioms fusedMap4624_checked
#print axioms certified4624
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
