/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4575 : Family 10 := level10.get ⟨524,by decide⟩
def sourceMap4575 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4575 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4575_checked : acceptsGraphIso
    (source (graph core4575) (root 10) 2 2) DegreeTwoThreeSpectrum7129.graph sourceMap4575=true := by decide +kernel
theorem fusedMap4575_checked : acceptsGraphIso
    (fused (graph core4575) (root 10) 2 2) DegreeTwoThreeSpectrum5167.graph fusedMap4575=true := by decide +kernel
theorem certified4575 : Certified (graph core4575) (root 10) 2 2 :=
  of_native_maps core4575 DegreeTwoThreeSpectrum7129.graph DegreeTwoThreeSpectrum5167.graph
    sourceMap4575 fusedMap4575 sourceMap4575_checked fusedMap4575_checked
    DegreeTwoThreeFiniteComparisons.comparison4575
#print axioms sourceMap4575_checked
#print axioms fusedMap4575_checked
#print axioms certified4575
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
