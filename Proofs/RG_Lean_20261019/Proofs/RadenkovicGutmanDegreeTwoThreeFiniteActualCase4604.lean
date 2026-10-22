/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4604 : Family 10 := level10.get ⟨611,by decide⟩
def sourceMap4604 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4604 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4604_checked : acceptsGraphIso
    (source (graph core4604) (root 10) 2 2) DegreeTwoThreeSpectrum7251.graph sourceMap4604=true := by decide +kernel
theorem fusedMap4604_checked : acceptsGraphIso
    (fused (graph core4604) (root 10) 2 2) DegreeTwoThreeSpectrum5294.graph fusedMap4604=true := by decide +kernel
theorem certified4604 : Certified (graph core4604) (root 10) 2 2 :=
  of_native_maps core4604 DegreeTwoThreeSpectrum7251.graph DegreeTwoThreeSpectrum5294.graph
    sourceMap4604 fusedMap4604 sourceMap4604_checked fusedMap4604_checked
    DegreeTwoThreeFiniteComparisons.comparison4604
#print axioms sourceMap4604_checked
#print axioms fusedMap4604_checked
#print axioms certified4604
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
