/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4618 : Family 10 := level10.get ⟨650,by decide⟩
def sourceMap4618 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4618 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4618_checked : acceptsGraphIso
    (source (graph core4618) (root 10) 2 2) DegreeTwoThreeSpectrum7301.graph sourceMap4618=true := by decide +kernel
theorem fusedMap4618_checked : acceptsGraphIso
    (fused (graph core4618) (root 10) 2 2) DegreeTwoThreeSpectrum5352.graph fusedMap4618=true := by decide +kernel
theorem certified4618 : Certified (graph core4618) (root 10) 2 2 :=
  of_native_maps core4618 DegreeTwoThreeSpectrum7301.graph DegreeTwoThreeSpectrum5352.graph
    sourceMap4618 fusedMap4618 sourceMap4618_checked fusedMap4618_checked
    DegreeTwoThreeFiniteComparisons.comparison4618
#print axioms sourceMap4618_checked
#print axioms fusedMap4618_checked
#print axioms certified4618
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
