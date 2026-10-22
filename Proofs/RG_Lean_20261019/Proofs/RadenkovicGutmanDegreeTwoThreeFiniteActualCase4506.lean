/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4506 : Family 10 := level10.get ⟨308,by decide⟩
def sourceMap4506 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4506 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4506_checked : acceptsGraphIso
    (source (graph core4506) (root 10) 2 2) DegreeTwoThreeSpectrum6618.graph sourceMap4506=true := by decide +kernel
theorem fusedMap4506_checked : acceptsGraphIso
    (fused (graph core4506) (root 10) 2 2) DegreeTwoThreeSpectrum5498.graph fusedMap4506=true := by decide +kernel
theorem certified4506 : Certified (graph core4506) (root 10) 2 2 :=
  of_native_maps core4506 DegreeTwoThreeSpectrum6618.graph DegreeTwoThreeSpectrum5498.graph
    sourceMap4506 fusedMap4506 sourceMap4506_checked fusedMap4506_checked
    DegreeTwoThreeFiniteComparisons.comparison4506
#print axioms sourceMap4506_checked
#print axioms fusedMap4506_checked
#print axioms certified4506
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
