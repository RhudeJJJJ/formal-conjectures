/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4610 : Family 10 := level10.get ⟨631,by decide⟩
def sourceMap4610 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4610 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4610_checked : acceptsGraphIso
    (source (graph core4610) (root 10) 2 2) DegreeTwoThreeSpectrum7289.graph sourceMap4610=true := by decide +kernel
theorem fusedMap4610_checked : acceptsGraphIso
    (fused (graph core4610) (root 10) 2 2) DegreeTwoThreeSpectrum5323.graph fusedMap4610=true := by decide +kernel
theorem certified4610 : Certified (graph core4610) (root 10) 2 2 :=
  of_native_maps core4610 DegreeTwoThreeSpectrum7289.graph DegreeTwoThreeSpectrum5323.graph
    sourceMap4610 fusedMap4610 sourceMap4610_checked fusedMap4610_checked
    DegreeTwoThreeFiniteComparisons.comparison4610
#print axioms sourceMap4610_checked
#print axioms fusedMap4610_checked
#print axioms certified4610
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
