/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4505 : Family 10 := level10.get ⟨302,by decide⟩
def sourceMap4505 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4505 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4505_checked : acceptsGraphIso
    (source (graph core4505) (root 10) 2 2) DegreeTwoThreeSpectrum6575.graph sourceMap4505=true := by decide +kernel
theorem fusedMap4505_checked : acceptsGraphIso
    (fused (graph core4505) (root 10) 2 2) DegreeTwoThreeSpectrum5480.graph fusedMap4505=true := by decide +kernel
theorem certified4505 : Certified (graph core4505) (root 10) 2 2 :=
  of_native_maps core4505 DegreeTwoThreeSpectrum6575.graph DegreeTwoThreeSpectrum5480.graph
    sourceMap4505 fusedMap4505 sourceMap4505_checked fusedMap4505_checked
    DegreeTwoThreeFiniteComparisons.comparison4505
#print axioms sourceMap4505_checked
#print axioms fusedMap4505_checked
#print axioms certified4505
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
