/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4534 : Family 10 := level10.get ⟨401,by decide⟩
def sourceMap4534 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4534 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4534_checked : acceptsGraphIso
    (source (graph core4534) (root 10) 2 2) DegreeTwoThreeSpectrum6810.graph sourceMap4534=true := by decide +kernel
theorem fusedMap4534_checked : acceptsGraphIso
    (fused (graph core4534) (root 10) 2 2) DegreeTwoThreeSpectrum5758.graph fusedMap4534=true := by decide +kernel
theorem certified4534 : Certified (graph core4534) (root 10) 2 2 :=
  of_native_maps core4534 DegreeTwoThreeSpectrum6810.graph DegreeTwoThreeSpectrum5758.graph
    sourceMap4534 fusedMap4534 sourceMap4534_checked fusedMap4534_checked
    DegreeTwoThreeFiniteComparisons.comparison4534
#print axioms sourceMap4534_checked
#print axioms fusedMap4534_checked
#print axioms certified4534
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
