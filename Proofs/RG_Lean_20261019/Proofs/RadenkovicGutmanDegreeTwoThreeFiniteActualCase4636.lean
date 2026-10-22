/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4636 : Family 10 := level10.get ⟨704,by decide⟩
def sourceMap4636 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4636 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4636_checked : acceptsGraphIso
    (source (graph core4636) (root 10) 2 2) DegreeTwoThreeSpectrum7362.graph sourceMap4636=true := by decide +kernel
theorem fusedMap4636_checked : acceptsGraphIso
    (fused (graph core4636) (root 10) 2 2) DegreeTwoThreeSpectrum5445.graph fusedMap4636=true := by decide +kernel
theorem certified4636 : Certified (graph core4636) (root 10) 2 2 :=
  of_native_maps core4636 DegreeTwoThreeSpectrum7362.graph DegreeTwoThreeSpectrum5445.graph
    sourceMap4636 fusedMap4636 sourceMap4636_checked fusedMap4636_checked
    DegreeTwoThreeFiniteComparisons.comparison4636
#print axioms sourceMap4636_checked
#print axioms fusedMap4636_checked
#print axioms certified4636
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
