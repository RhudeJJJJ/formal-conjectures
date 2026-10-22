/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4500 : Family 10 := level10.get ⟨281,by decide⟩
def sourceMap4500 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4500 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4500_checked : acceptsGraphIso
    (source (graph core4500) (root 10) 2 2) DegreeTwoThreeSpectrum6455.graph sourceMap4500=true := by decide +kernel
theorem fusedMap4500_checked : acceptsGraphIso
    (fused (graph core4500) (root 10) 2 2) DegreeTwoThreeSpectrum5419.graph fusedMap4500=true := by decide +kernel
theorem certified4500 : Certified (graph core4500) (root 10) 2 2 :=
  of_native_maps core4500 DegreeTwoThreeSpectrum6455.graph DegreeTwoThreeSpectrum5419.graph
    sourceMap4500 fusedMap4500 sourceMap4500_checked fusedMap4500_checked
    DegreeTwoThreeFiniteComparisons.comparison4500
#print axioms sourceMap4500_checked
#print axioms fusedMap4500_checked
#print axioms certified4500
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
