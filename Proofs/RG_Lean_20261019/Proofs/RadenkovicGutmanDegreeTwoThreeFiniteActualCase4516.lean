/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4516 : Family 10 := level10.get ⟨346,by decide⟩
def sourceMap4516 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4516 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4516_checked : acceptsGraphIso
    (source (graph core4516) (root 10) 2 2) DegreeTwoThreeSpectrum6771.graph sourceMap4516=true := by decide +kernel
theorem fusedMap4516_checked : acceptsGraphIso
    (fused (graph core4516) (root 10) 2 2) DegreeTwoThreeSpectrum5612.graph fusedMap4516=true := by decide +kernel
theorem certified4516 : Certified (graph core4516) (root 10) 2 2 :=
  of_native_maps core4516 DegreeTwoThreeSpectrum6771.graph DegreeTwoThreeSpectrum5612.graph
    sourceMap4516 fusedMap4516 sourceMap4516_checked fusedMap4516_checked
    DegreeTwoThreeFiniteComparisons.comparison4516
#print axioms sourceMap4516_checked
#print axioms fusedMap4516_checked
#print axioms certified4516
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
