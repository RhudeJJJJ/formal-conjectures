/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4609 : Family 10 := level10.get ⟨630,by decide⟩
def sourceMap4609 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4609 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4609_checked : acceptsGraphIso
    (source (graph core4609) (root 10) 2 2) DegreeTwoThreeSpectrum7290.graph sourceMap4609=true := by decide +kernel
theorem fusedMap4609_checked : acceptsGraphIso
    (fused (graph core4609) (root 10) 2 2) DegreeTwoThreeSpectrum5321.graph fusedMap4609=true := by decide +kernel
theorem certified4609 : Certified (graph core4609) (root 10) 2 2 :=
  of_native_maps core4609 DegreeTwoThreeSpectrum7290.graph DegreeTwoThreeSpectrum5321.graph
    sourceMap4609 fusedMap4609 sourceMap4609_checked fusedMap4609_checked
    DegreeTwoThreeFiniteComparisons.comparison4609
#print axioms sourceMap4609_checked
#print axioms fusedMap4609_checked
#print axioms certified4609
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
