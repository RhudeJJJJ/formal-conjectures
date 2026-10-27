/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4577 : Family 10 := level10.get ⟨531,by decide⟩
def sourceMap4577 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4577 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4577_checked : acceptsGraphIso
    (source (graph core4577) (root 10) 2 2) DegreeTwoThreeSpectrum7142.graph sourceMap4577=true := by decide +kernel
theorem fusedMap4577_checked : acceptsGraphIso
    (fused (graph core4577) (root 10) 2 2) DegreeTwoThreeSpectrum5176.graph fusedMap4577=true := by decide +kernel
theorem certified4577 : Certified (graph core4577) (root 10) 2 2 :=
  of_native_maps core4577 DegreeTwoThreeSpectrum7142.graph DegreeTwoThreeSpectrum5176.graph
    sourceMap4577 fusedMap4577 sourceMap4577_checked fusedMap4577_checked
    DegreeTwoThreeFiniteComparisons.comparison4577
#print axioms sourceMap4577_checked
#print axioms fusedMap4577_checked
#print axioms certified4577
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
